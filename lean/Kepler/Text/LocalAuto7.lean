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
import Kepler.Text.AzimBridge
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto9
import Kepler.Text.LocalAuto35
import Kepler.Text.LocalAuto37
import Mathlib

set_option maxHeartbeats 5000000

-- W6a (SF-54 import of AzimBridge/LA3): keep the pre-import `DecidableEq
-- (V3 × V3)` resolution.  LA3's global `dartDecEq3` (`Classical.decEq`, not
-- defeq to Mathlib's product instance) would otherwise win synthesis and
-- change the meaning of the already-proved `hypermapOfFan` code below; the
-- local priority boost restores the old-instance behavior file-wide.
attribute [local instance 2000] instDecidableEqProd

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

/-- HOL `ANGLES_ADD_AFF_GE` (polar_fan.hl:74). -/
theorem ANGLES_ADD_AFF_GE {u v w x : V3} (hv : v ≠ u) (hw : w ≠ u) (hx : x ≠ u)
    (hmem : x ∈ affGt {u} {v, w}) :
    EuclideanGeometry.angle v u x + EuclideanGeometry.angle x u w
      = EuclideanGeometry.angle v u w := by
  by_cases hvw : v = w
  · -- degenerate: w = v, so x lies on the open ray u → v
    subst w
    have hmem1 : x ∈ affGt {u} {v} := by simpa using hmem
    obtain ⟨f, hfin, hxsum, hpos, hone⟩ := hmem1
    have hsum : ∑ z ∈ hfin.toFinset, f z = f u + f v := sum_insert_single_s hfin hv.symm
    have hsumv : ∑ z ∈ hfin.toFinset, f z • z = f u • u + f v • v :=
      sum_insert_single_v hfin hv.symm
    rw [hsum] at hone
    have hfv : 0 < f v := hpos v (by simp)
    have hxu : x - u = f v • (v - u) := by
      rw [hxsum, hsumv]
      have hfu : f u = 1 - f v := by linarith
      rw [hfu, sub_smul]
      module
    have h1 : EuclideanGeometry.angle v u x = EuclideanGeometry.angle v u v :=
      EuclideanGeometry.angle_smul_right_of_pos v hfv (by simpa [vsub_eq_sub] using hxu.symm)
    have h2 : EuclideanGeometry.angle x u v = EuclideanGeometry.angle v u v :=
      EuclideanGeometry.angle_smul_left_of_pos v hfv (by simpa [vsub_eq_sub] using hxu.symm)
    rw [h1, h2, EuclideanGeometry.angle_self_of_ne hv]
    ring
  · -- v ≠ w: extract x = u + f v • (v-u) + f w • (w-u) with positive coefficients
    obtain ⟨f, hfin, hxsum, hpos, hone⟩ := hmem
    have hsums : ∑ z ∈ hfin.toFinset, f z = f u + f v + f w :=
      sum_insert_pair_s hfin hv.symm hw.symm hvw
    have hsumv : ∑ z ∈ hfin.toFinset, f z • z = f u • u + f v • v + f w • w :=
      sum_insert_pair_v hfin hv.symm hw.symm hvw
    rw [hsums] at hone
    have hrv : 0 < f v := hpos v (by simp)
    have hsw : 0 < f w := hpos w (by simp)
    have hrs : 0 < f v + f w := add_pos hrv hsw
    have hrsne : f v + f w ≠ 0 := hrs.ne'
    have hxu : x - u = f v • (v - u) + f w • (w - u) := by
      rw [hxsum, hsumv]
      have hfu : f u = 1 - f v - f w := by linarith
      rw [hfu, sub_smul]
      module
    -- x' := u + (fv+fw)⁻¹ • (x-u) lies strictly inside the segment [v,w]
    let x' : V3 := u + (f v + f w)⁻¹ • (x - u)
    have hx'u : (f v + f w) • (x' - u) = x - u := by
      show (f v + f w) • (u + (f v + f w)⁻¹ • (x - u) - u) = x - u
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hrsne, one_smul]
    have hx'sub : x' - u =
        (f v / (f v + f w)) • (v - u) + (f w / (f v + f w)) • (w - u) := by
      show u + (f v + f w)⁻¹ • (x - u) - u = _
      rw [add_sub_cancel_left, hxu, smul_add, smul_smul, smul_smul, div_eq_inv_mul,
        div_eq_inv_mul]
    have hx'line : x' = AffineMap.lineMap v w (f w / (f v + f w)) := by
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      have hx' : x' = u + (x' - u) := by abel
      rw [hx', hx'sub]
      have hab : f v / (f v + f w) + f w / (f v + f w) = 1 := by
        rw [← add_div, div_self hrsne]
      have ha : f v / (f v + f w) = 1 - f w / (f v + f w) := by linarith
      rw [ha]
      module
    have hW : Wbtw ℝ v x' w := by
      rw [Wbtw, affineSegment, Set.mem_image]
      refine ⟨f w / (f v + f w), ⟨div_pos hsw hrs |>.le, ?_⟩, hx'line.symm⟩
      rw [div_le_one hrs]
      linarith
    have h1 : EuclideanGeometry.angle v u x = EuclideanGeometry.angle v u x' :=
      EuclideanGeometry.angle_smul_right_of_pos v hrs (by simpa [vsub_eq_sub] using hx'u)
    have h2 : EuclideanGeometry.angle x u w = EuclideanGeometry.angle x' u w :=
      EuclideanGeometry.angle_smul_left_of_pos w hrs (by simpa [vsub_eq_sub] using hx'u)
    calc EuclideanGeometry.angle v u x + EuclideanGeometry.angle x u w
        = EuclideanGeometry.angle v u x' + EuclideanGeometry.angle x' u w := by rw [h1, h2]
      _ = EuclideanGeometry.angle v u w :=
        EuclideanGeometry.angle_add_of_ne_of_ne hv.symm hw.symm hW

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

/-! ### W6a p2-bridge kit (SF-54 construction path; private support for the
nine foundation stubs below)

Construction path (la1-localfan-scout §6): `hedge` + LA1 `LocalFan` →
`localFan_p2.of_LocalFan_noIso` (AzimBridge, already real) lands in the
faithful `_p2` world, where LA2's `WRGCVDR` kit applies.  `rhoNode1` /
`ivsRhoNode1` (LA1) and `rhoNode1_p2` / `ivsRhoNode1_p2` (LA2) are the same
`Classical.epsilon` construction (defeq), so the p2 facts transfer verbatim.
NOTE: `LocalAuto5` is NOT importable next to `LocalAuto1` (both environments
declare `AFF_GE_MONO_TRANS`, via `PackingAuto18` resp. locally), so the
p2-spine lemmas (`IVS_RHO_IDD`, `LOFA_IMP_ITER_RHO_NODE_ID`, the orbit-cycle
engine, ...) are rebuilt here from LA2's real `WRGCVDR_BIJ` / `WRGCVDR_ORBIT`
instead of imported. -/

/-- SF-54 bridge: `LocalFan` + hedge lands in the faithful `_p2` world. -/
private theorem w6a_to_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : localFan_p2 V E FF :=
  localFan_p2.of_LocalFan_noIso h hedge

/-- `Classical.epsilon` collapse when the predicate holds at one point only
(LA5 `epsilonFixed` copy; renders HOL `(@w. P w)` under a uniqueness
hypothesis). -/
private theorem w6a_epsilon_fixed {α : Type*} [Nonempty α] {p : α → Prop} {a : α} (hpa : p a)
    (huniq : ∀ y, p y → y = a) : Classical.epsilon p = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- Lane support (LA5 r3 copy): `q`-periodic points stay fixed under multiples
of the period. -/
private theorem w6a_period_mul {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (k : ℕ) : f^[k * q] x = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, hqx, ih]

/-- Lane support (LA5 r3 copy): index reduction modulo a period. -/
private theorem w6a_period_mod {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (n : ℕ) : f^[n] x = f^[n % q] x := by
  have hsplit : n / q * q + n % q = n := Nat.div_add_mod' n q
  have hqx' : f^[q] (f^[n % q] x) = f^[n % q] x := by
    rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hqx]
  calc f^[n] x = f^[n / q * q + n % q] x := by rw [hsplit]
    _ = f^[n / q * q] (f^[n % q] x) := Function.iterate_add_apply f (n / q * q) (n % q) x
    _ = f^[n % q] x := w6a_period_mul f hqx' (n / q)

/-- Lane support (LA5 r3 copy): under the orbit condition, coinciding iterates
of a point force it to be periodic with the index difference. -/
private theorem w6a_orbit_key {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ x ∈ V, orbitF_p2 f x = V) {x : α} (hx : x ∈ V) {i j : ℕ}
    (hij2 : i ≤ j) (hij : f^[i] x = f^[j] x) : f^[j - i] x = x := by
  have hEq : j - i + i = j := by omega
  have hy : f^[j] x = f^[j - i] (f^[i] x) := by
    have h := Function.iterate_add_apply f (j - i) i x
    rwa [hEq] at h
  have hmem : ∀ n : ℕ, f^[n] x ∈ V := by
    intro n
    rw [← horb x hx]
    exact ⟨n, rfl⟩
  have hyV : f^[i] x ∈ V := hmem i
  have hxO : x ∈ orbitF_p2 f (f^[i] x) := by rw [horb (f^[i] x) hyV]; exact hx
  obtain ⟨t, hxt⟩ := hxO
  have hfix : f^[j - i] (f^[i] x) = f^[i] x := hy.symm.trans hij.symm
  calc f^[j - i] x = f^[j - i] (f^[t] (f^[i] x)) := by rw [hxt]
    _ = f^[(j - i) + t] (f^[i] x) := (Function.iterate_add_apply f (j - i) t (f^[i] x)).symm
    _ = f^[t + (j - i)] (f^[i] x) := by rw [Nat.add_comm]
    _ = f^[t] (f^[j - i] (f^[i] x)) := Function.iterate_add_apply f t (j - i) (f^[i] x)
    _ = f^[t] (f^[i] x) := by rw [hfix]
    _ = x := hxt

/-- Lane support (LA5 r3 copy): the orbit condition makes `V` a finite cycle;
`p` is a common period with `0 < p`, the first `p` iterates are pairwise
distinct and exhaust `V`, and `V.ncard = p`. -/
private theorem w6a_orbit_cycle {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ x ∈ V, orbitF_p2 f x = V) {x : α} (hx : x ∈ V) :
    ∃ p : ℕ, 0 < p ∧ f^[p] x = x ∧
      (∀ i j : ℕ, i < j → j < p → f^[i] x ≠ f^[j] x) ∧
      ({f^[n] x | n < p} : Set α) = V ∧ V.ncard = p := by
  have hmem : ∀ n : ℕ, f^[n] x ∈ V := by
    intro n
    rw [← horb x hx]
    exact ⟨n, rfl⟩
  have hper : ∃ p : ℕ, 0 < p ∧ f^[p] x = x := by
    have hfx : f x ∈ V := hmem 1
    have hxO : x ∈ orbitF_p2 f (f x) := by rw [horb (f x) hfx]; exact hx
    obtain ⟨n, hn⟩ := hxO
    exact ⟨n + 1, Nat.succ_pos n, by rw [Function.iterate_succ_apply f n x]; exact hn⟩
  have hex : ∃ n, 0 < n ∧ f^[n] x = x := hper
  have hp0 : 0 < Nat.find hex := (Nat.find_spec hex).1
  have hpx : f^[Nat.find hex] x = x := (Nat.find_spec hex).2
  have hmin : ∀ m : ℕ, 0 < m → m < Nat.find hex → f^[m] x ≠ x :=
    fun m hm0 hmlt hcon => Nat.find_min hex hmlt ⟨hm0, hcon⟩
  have hkey : ∀ i j : ℕ, i ≤ j → f^[i] x = f^[j] x → f^[j - i] x = x :=
    fun i j hle hij' => w6a_orbit_key horb hx hle hij'
  have hdis : ∀ i j : ℕ, i < j → j < Nat.find hex → f^[i] x ≠ f^[j] x := by
    intro i j hij hjp hcon
    exact hmin (j - i) (by omega) (by omega) (hkey i j (Nat.le_of_lt hij) hcon)
  have hset : ({f^[n] x | n < Nat.find hex} : Set α) = V := by
    ext y
    constructor
    · rintro ⟨n, -, rfl⟩
      exact hmem n
    · intro hy
      have hYO : y ∈ orbitF_p2 f x := by rw [horb x hx]; exact hy
      obtain ⟨m, hm⟩ := hYO
      refine ⟨m % Nat.find hex, Nat.mod_lt _ hp0, ?_⟩
      rw [← w6a_period_mod f hpx m]
      exact hm
  have hcard : V.ncard = Nat.find hex := by
    have himage : ({f^[n] x | n < Nat.find hex} : Set α) =
        (fun n : ℕ => f^[n] x) '' Set.Iio (Nat.find hex) := rfl
    rw [← hset, himage]
    have hInj : Set.InjOn (fun n : ℕ => f^[n] x) (Set.Iio (Nat.find hex)) := by
      intro i hi j hj hcon
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact absurd hcon (hdis i j h (Set.mem_Iio.mp hj))
      · exact h
      · exact absurd hcon.symm (hdis j i h (Set.mem_Iio.mp hi))
    rw [Set.InjOn.ncard_image hInj]
    exact Set.ncard_Iio_nat _
  exact ⟨Nat.find hex, hp0, hpx, hdis, hset, hcard⟩

/-- The rho-node sends every dart to its second component (LA5
`DETER_RHO_NODE` copy; `WRGCVDR_BIJ` makes the first components of darts
injective, so the epsilon is determined). -/
private theorem w6a_deter {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v w : V3} (hw : (v, w) ∈ FF) : rhoNode1_p2 FF v = w := by
  have huniq : ∀ y : V3, (v, y) ∈ FF → y = w := fun y hy =>
    (congrArg Prod.snd ((WRGCVDR_BIJ h).2.1 hw hy rfl)).symm
  exact w6a_epsilon_fixed hw huniq

/-- `(v, rho v)` is a dart for every vertex (LA5 `LOCAL_FAN_RHO_NODE_PROS`
first half; from the `WRGCVDR_BIJ` surjectivity). -/
private theorem w6a_rho_pros_left {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {x : V3} (hx : x ∈ V) : (x, rhoNode1_p2 FF x) ∈ FF := by
  obtain ⟨-, -, hsurj⟩ := WRGCVDR_BIJ h
  obtain ⟨d, hd, hfd⟩ := hsurj hx
  have hdeq : (x, d.2) = d := Prod.ext hfd.symm rfl
  have hmemFF : (x, d.2) ∈ FF := by
    rw [hdeq]
    exact hd
  exact Classical.epsilon_spec (p := fun w => (x, w) ∈ FF) ⟨d.2, hmemFF⟩

/-- All rho-iterates stay in `V` (LA5 `LOCAL_FAN_ITER_RHO_NODE_IN_V` copy). -/
private theorem w6a_iter_rho_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∀ i : ℕ, (rhoNode1_p2 FF)^[i] v ∈ V := by
  intro i
  have h1 : (rhoNode1_p2 FF)^[i] v ∈ orbitF_p2 (rhoNode1_p2 FF) v := ⟨i, rfl⟩
  rwa [WRGCVDR_ORBIT h v hv] at h1

/-- HOL `LOFA_IMP_ITER_RHO_NODE_ID` (p2 world). -/
private theorem w6a_iter_rho_card {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    (rhoNode1_p2 FF)^[V.ncard] v = v := by
  obtain ⟨p, hp0, hpx, -, -, hcard⟩ := w6a_orbit_cycle (fun x hx => WRGCVDR_ORBIT h x hx) hv
  rw [hcard]
  exact hpx

/-- `V.ncard` is positive on a local fan. -/
private theorem w6a_vcard_pos {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) : 0 < V.ncard := by
  obtain ⟨p, hp0, -, -, -, hcard⟩ := w6a_orbit_cycle (fun x hx => WRGCVDR_ORBIT h x hx) hv
  rwa [hcard]

/-- `rho` is injective on `V` (LA5 `LOFA_IMP_BIJ_VV` InjOn half; reads
`rho a = rho b` through the minimal cycle). -/
private theorem w6a_injOn_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {a b : V3} (ha : a ∈ V) (hb : b ∈ V)
    (hab : rhoNode1_p2 FF a = rhoNode1_p2 FF b) : a = b := by
  have horb : ∀ x ∈ V, orbitF_p2 (rhoNode1_p2 FF) x = V :=
    fun x hx => WRGCVDR_ORBIT h x hx
  obtain ⟨p, hp0, hpx, hdis, hcover, -⟩ := w6a_orbit_cycle horb ha
  rw [← hcover] at hb
  obtain ⟨ib, hiblt, hib⟩ := hb
  by_cases hib0 : ib = 0
  · rw [hib0, Function.iterate_zero_apply] at hib
    exact hib
  · have hp1 : 1 ≤ ib := by omega
    have hap : (rhoNode1_p2 FF)^[ib + 1] a
        = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[ib] a) :=
      Function.iterate_succ_apply' _ _ _
    have hstep : rhoNode1_p2 FF a = (rhoNode1_p2 FF)^[ib + 1] a := by
      rw [hap]
      rw [← hib] at hab
      exact hab
    by_cases hlt : ib + 1 < p
    · exact absurd hstep (hdis 1 (ib + 1) (by omega) hlt)
    · have heqp : ib + 1 = p := by omega
      rw [heqp, hpx] at hstep
      have hq1 : (rhoNode1_p2 FF)^[1] a = a := hstep
      have h9 : (rhoNode1_p2 FF)^[ib] a
          = (rhoNode1_p2 FF)^[ib % 1] a := w6a_period_mod _ hq1 ib
      rw [← hib, h9, Nat.mod_one, Function.iterate_zero_apply]

/-- On the fan the ivs-node is the `(CARD V - 1)`-th rho iterate (the
predecessor on the cycle). -/
private theorem w6a_ivs_eq_rho_pred {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {u : V3} (hu : u ∈ V) :
    ivsRhoNode1_p2 FF u = (rhoNode1_p2 FF)^[V.ncard - 1] u := by
  have hp0 := w6a_vcard_pos h hu
  have hzV : (rhoNode1_p2 FF)^[V.ncard - 1] u ∈ V := w6a_iter_rho_mem h hu (V.ncard - 1)
  have hru : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[V.ncard - 1] u) = u := by
    have hiter : (rhoNode1_p2 FF)^[(V.ncard - 1) + 1] u
        = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[V.ncard - 1] u) :=
      Function.iterate_succ_apply' _ _ _
    have hsum : (V.ncard - 1) + 1 = V.ncard := by omega
    rw [hsum, w6a_iter_rho_card h hu] at hiter
    exact hiter.symm
  have hpro : ((rhoNode1_p2 FF)^[V.ncard - 1] u,
      rhoNode1_p2 FF ((rhoNode1_p2 FF)^[V.ncard - 1] u)) ∈ FF :=
    w6a_rho_pros_left h hzV
  rw [hru] at hpro
  have huniq : ∀ ww : V3, (ww, u) ∈ FF → ww = (rhoNode1_p2 FF)^[V.ncard - 1] u := by
    intro ww hww
    have hwv : ww ∈ V := (WRGCVDR_BIJ h).1 hww
    have hd1 : rhoNode1_p2 FF ww = u := w6a_deter h hww
    exact w6a_injOn_rho h hwv hzV (hd1.trans hru.symm)
  exact w6a_epsilon_fixed hpro huniq

/-- HOL `IVS_RHO_IDD` (p2 world). -/
private theorem w6a_ivs_idd {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ivsRhoNode1_p2 FF (rhoNode1_p2 FF v) = v := by
  have hrV : rhoNode1_p2 FF v ∈ V := w6a_iter_rho_mem h hv 1
  have h1 := w6a_ivs_eq_rho_pred h hrV
  have hsplit := Function.iterate_add_apply (rhoNode1_p2 FF) (V.ncard - 1) 1 v
  have hone : (rhoNode1_p2 FF)^[1] v = rhoNode1_p2 FF v := rfl
  have hp0 := w6a_vcard_pos h hv
  have hsum : (V.ncard - 1) + 1 = V.ncard := by omega
  rw [hone, hsum] at hsplit
  rw [h1, ← hsplit]
  exact w6a_iter_rho_card h hv

/-- `ivs v` lies in `V`. -/
private theorem w6a_ivs_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) : ivsRhoNode1_p2 FF v ∈ V := by
  rw [w6a_ivs_eq_rho_pred h hv]
  exact w6a_iter_rho_mem h hv (V.ncard - 1)

/-- HOL `RHO_IVS_IDD` (mirror of `IVS_RHO_IDD`, p2 world). -/
private theorem w6a_rho_ivs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := by
  rw [w6a_ivs_eq_rho_pred h hv]
  have hp0 := w6a_vcard_pos h hv
  have hsucc := Function.iterate_succ_apply' (rhoNode1_p2 FF) (V.ncard - 1) v
  have hsum : (V.ncard - 1) + 1 = V.ncard := by omega
  rw [Nat.succ_eq_add_one, hsum] at hsucc
  rw [← hsucc, w6a_iter_rho_card h hv]

/-- ivs-iterates are rho-iterates: `(ivs)^[n] u = rho^[n * (p - 1)] u`. -/
private theorem w6a_iter_ivs_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {u : V3} (hu : u ∈ V) (n : ℕ) :
    (ivsRhoNode1_p2 FF)^[n] u = (rhoNode1_p2 FF)^[n * (V.ncard - 1)] u := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hcur : (ivsRhoNode1_p2 FF)^[k] u ∈ V := by
      rw [ih]
      exact w6a_iter_rho_mem h hu (k * (V.ncard - 1))
    have hstep : (ivsRhoNode1_p2 FF)^[k + 1] u
        = ivsRhoNode1_p2 FF ((ivsRhoNode1_p2 FF)^[k] u) :=
      Function.iterate_succ_apply' _ _ _
    rw [hstep, w6a_ivs_eq_rho_pred h hcur, ih]
    rw [← Function.iterate_add_apply (rhoNode1_p2 FF) (V.ncard - 1) (k * (V.ncard - 1)) u]
    have hexp : (V.ncard - 1) + k * (V.ncard - 1) = (k + 1) * (V.ncard - 1) := by ring
    rw [hexp]

/-- iterates of ivs stay in `V`. -/
private theorem w6a_iter_ivs_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∀ i : ℕ, (ivsRhoNode1_p2 FF)^[i] v ∈ V := by
  intro i
  rw [w6a_iter_ivs_eq h hv i]
  exact w6a_iter_rho_mem h hv (i * (V.ncard - 1))

/-- HOL `ITER_IVS_RHO_IDD` (p2 world). -/
private theorem w6a_iter_ivs_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∀ n : ℕ, (ivsRhoNode1_p2 FF)^[n] ((rhoNode1_p2 FF)^[n] v) = v := by
  intro n
  have hrnV : (rhoNode1_p2 FF)^[n] v ∈ V := w6a_iter_rho_mem h hv n
  have hshift := w6a_iter_ivs_eq h hrnV n
  rw [hshift]
  rw [← Function.iterate_add_apply (rhoNode1_p2 FF) (n * (V.ncard - 1)) n v]
  have hp0 := w6a_vcard_pos h hv
  have hp1 : (V.ncard - 1) + 1 = V.ncard := by omega
  have h2 : n * ((V.ncard - 1) + 1) = n * (V.ncard - 1) + n := by
    rw [Nat.mul_add, Nat.mul_one]
  have hmul : n * (V.ncard - 1) + n = n * V.ncard := by
    rw [← h2, hp1]
  rw [hmul]
  exact w6a_period_mul _ (w6a_iter_rho_card h hv) n

/-- HOL `ITER_RHO_IVS_IDD` (p2 world). -/
private theorem w6a_iter_rho_ivs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∀ n : ℕ, (rhoNode1_p2 FF)^[n] ((ivsRhoNode1_p2 FF)^[n] v) = v := by
  intro n
  have hshift := w6a_iter_ivs_eq h hv n
  rw [hshift]
  rw [← Function.iterate_add_apply (rhoNode1_p2 FF) n (n * (V.ncard - 1)) v]
  have hp0 := w6a_vcard_pos h hv
  have hp1 : (V.ncard - 1) + 1 = V.ncard := by omega
  have h2 : n * ((V.ncard - 1) + 1) = n * (V.ncard - 1) + n := by
    rw [Nat.mul_add, Nat.mul_one]
  have hmul : n + n * (V.ncard - 1) = n * V.ncard := by
    rw [Nat.add_comm, ← h2, hp1]
  rw [hmul]
  exact w6a_period_mul _ (w6a_iter_rho_card h hv) n

/-- `rho` is injective on `V` (telescope form via `IVS_RHO_IDD`). -/
private theorem w6a_rho_inj {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v w : V3} (hv : v ∈ V) (hw : w ∈ V)
    (hcon : rhoNode1_p2 FF v = rhoNode1_p2 FF w) : v = w := by
  have h1 : ivsRhoNode1_p2 FF (rhoNode1_p2 FF v) = ivsRhoNode1_p2 FF (rhoNode1_p2 FF w) := by
    rw [hcon]
  rwa [w6a_ivs_idd h hv, w6a_ivs_idd h hw] at h1

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT` (p2 world): the rho orbit of `v` is
all of `V`, with the index bounded by `V.ncard`. -/
private theorem w6a_orbit_index {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ V) :
    ∃ i : ℕ, i < V.ncard ∧ w = (rhoNode1_p2 FF)^[i] v := by
  obtain ⟨p, hp0, hpx, -, hset, hcard⟩ :=
    w6a_orbit_cycle (fun x hx => WRGCVDR_ORBIT h x hx) hv
  have hmem : w ∈ ({(rhoNode1_p2 FF)^[n] v | n < p} : Set V3) := by rw [hset]; exact hw
  obtain ⟨n, hn, hn'⟩ := hmem
  refine ⟨n, ?_, hn'.symm⟩
  rw [hcard]
  exact hn

/-- `(ivs)^[k] u = rho^[p - k] u` for `k ≤ p`. -/
private theorem w6a_ivs_iter_eq_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {u : V3} (hu : u ∈ V) {k : ℕ} (hk : k ≤ V.ncard) :
    (ivsRhoNode1_p2 FF)^[k] u = (rhoNode1_p2 FF)^[V.ncard - k] u := by
  have hshift := w6a_iter_ivs_eq h hu k
  have hper : (rhoNode1_p2 FF)^[V.ncard] ((ivsRhoNode1_p2 FF)^[k] u)
      = (ivsRhoNode1_p2 FF)^[k] u := w6a_iter_rho_card h (w6a_iter_ivs_mem h hu k)
  have htel : (rhoNode1_p2 FF)^[k] ((ivsRhoNode1_p2 FF)^[k] u) = u := w6a_iter_rho_ivs h hu k
  have hsplit : (rhoNode1_p2 FF)^[(V.ncard - k) + k] ((ivsRhoNode1_p2 FF)^[k] u)
      = (rhoNode1_p2 FF)^[V.ncard - k] ((rhoNode1_p2 FF)^[k] ((ivsRhoNode1_p2 FF)^[k] u)) :=
    Function.iterate_add_apply (rhoNode1_p2 FF) (V.ncard - k) k ((ivsRhoNode1_p2 FF)^[k] u)
  have hsum : (V.ncard - k) + k = V.ncard := by omega
  rw [hsum, htel] at hsplit
  calc (ivsRhoNode1_p2 FF)^[k] u = (rhoNode1_p2 FF)^[V.ncard] ((ivsRhoNode1_p2 FF)^[k] u) :=
      hper.symm
    _ = (rhoNode1_p2 FF)^[V.ncard - k] u := hsplit

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS` (p2 world). -/
private theorem w6a_orbit_index_ivs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ V) :
    ∃ i : ℕ, i < V.ncard ∧ w = (ivsRhoNode1_p2 FF)^[i] v := by
  obtain ⟨j, hj, hwj⟩ := w6a_orbit_index h hv hw
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    refine ⟨0, w6a_vcard_pos h hv, ?_⟩
    exact hwj
  · have hi : V.ncard - j < V.ncard := by omega
    refine ⟨V.ncard - j, hi, ?_⟩
    have heq := w6a_ivs_iter_eq_rho h hv (Nat.le_of_lt hi)
    rw [heq]
    have hdiff : V.ncard - (V.ncard - j) = j := by omega
    rw [hdiff]
    exact hwj

/-- HOL `RHO_NODE1_INJECTIVE` (polar_fan.hl:318). -/
theorem RHO_NODE1_INJECTIVE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    ∀ v ∈ V, ∀ w ∈ V, (rhoNode1 FF v = rhoNode1 FF w ↔ v = w) := by
  intro v hv w hw
  constructor
  · exact w6a_rho_inj (w6a_to_p2 h hedge) hv hw
  · intro he; rw [he]

/-- HOL `IVS_RHO_NODE1_IN_V` (polar_fan.hl:325). -/
theorem IVS_RHO_NODE1_IN_V {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : ∀ v ∈ V, ivsRhoNode1 FF v ∈ V := by
  intro v hv
  exact w6a_ivs_mem (w6a_to_p2 h hedge) hv

/-- HOL `LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V` (polar_fan.hl:330). -/
theorem LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) {v : V3} (hv : v ∈ V) (i : ℕ) :
    (ivsRhoNode1 FF)^[i] v ∈ V := by
  exact w6a_iter_ivs_mem (w6a_to_p2 h hedge) hv i

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT` (polar_fan.hl:336). -/
theorem LOCAL_FAN_ORBIT_MAP_EXPLICIT_LA7 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v w : V3) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ i, i < V.ncard ∧ w = (rhoNode1 FF)^[i] v := by
  exact w6a_orbit_index (w6a_to_p2 h hedge) hv hw

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS` (polar_fan.hl:360). -/
theorem LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v w : V3) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ i, i < V.ncard ∧ w = (ivsRhoNode1 FF)^[i] v := by
  exact w6a_orbit_index_ivs (w6a_to_p2 h hedge) hv hw

/-- HOL `ITER_IVS_RHO_IDD` (polar_fan.hl:381). -/
theorem ITER_IVS_RHO_IDD {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) (n : ℕ) :
    (ivsRhoNode1 FF)^[n] ((rhoNode1 FF)^[n] v) = v := by
  exact w6a_iter_ivs_rho (w6a_to_p2 h hedge) hv n

/-- HOL `ITER_RHO_IVS_IDD` (polar_fan.hl:392). -/
theorem ITER_RHO_IVS_IDD {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) (n : ℕ) :
    (rhoNode1 FF)^[n] ((ivsRhoNode1 FF)^[n] v) = v := by
  exact w6a_iter_rho_ivs (w6a_to_p2 h hedge) hv n

/-- HOL `LOFA_IMP_ITER_IVS_RHO_NODE_ID` (polar_fan.hl:402). -/
theorem LOFA_IMP_ITER_IVS_RHO_NODE_ID {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) :
    (ivsRhoNode1 FF)^[V.ncard] v = v := by
  have h1 := w6a_iter_ivs_rho (w6a_to_p2 h hedge) hv V.ncard
  rw [w6a_iter_rho_card (w6a_to_p2 h hedge) hv] at h1
  exact h1

/-- HOL `GENERIC_LOCAL_FAN_AZIM_POS` (polar_fan.hl:408). -/
-- Closed 2026-11-09 (wsewpch-w6a continuation).  The 2026-10-26 honest block
-- cited "EGHNAVX unported"; that is now stale (EGHNAVX landed at LA14:6965),
-- but LA14 is import-cyclic for LA7 (XivphksKit imports LA7), so the orbit
-- monotonicity is taken from the importable LA35 originals (`w2OrigMono_p35`,
-- `wSectorAt_p35`) and the planar-window interior-angle chain
-- (SUCCESSIVE_RHO_NODE1_AFF_LT -> TWO_SIDES -> OZQVSFF) is rebuilt below from
-- LA5/LA37 originals.  `w6a9_*` kit = verbatim LA14 copies (`w15_*` subset),
-- with `hedge` threaded explicitly; the world transfers (rhoNode1 /
-- rhoNode1_p2, interiorAngle1 / interiorAngle1_p2) are defeq.
private theorem w6a9_affGt_sub {s t : Set V3} : affGt s t ⊆ affGe s t := by
  intro v hv
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hv
  exact ⟨f, hfin, hsum, fun w hw => (hpos w hw).le, hone⟩

private theorem w6a9_ncol_third_notMem {a c d : V3}
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
  exact Collinear.subset hsub (collinear_pair (k := ℝ) (p₁ := a) (p₂ := c))

private theorem w6a9_ncol_mid_notMem {a c d : V3}
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
  exact Collinear.subset hsub (collinear_pair (k := ℝ) (p₁ := a) (p₂ := d))

private theorem w6a9_div_combo {t1 t2 t3 : ℝ} (ht3 : t3 ≠ 0) (hsum : t1 + t2 + t3 = 1) :
    -(t1 / t3) + -(t2 / t3) + 1 / t3 = 1 := by
  have h : -(t1 / t3) + -(t2 / t3) + 1 / t3 = (-t1 - t2 + 1) / t3 := by
    field_simp
    ring
  rw [h, div_eq_one_iff_eq ht3]
  linarith

private theorem w6a9_div_combo_vec {a b x y : V3} {t1 t2 t3 : ℝ} (ht3 : t3 ≠ 0)
    (hy : y = t1 • a + t2 • b + t3 • x) :
    x = (-(t1 / t3)) • a + (-(t2 / t3)) • b + (1 / t3) • y := by
  subst hy
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  have h1 : (1 / t3) * t3 = 1 := by field_simp
  have h2 : (1 / t3) * t1 = t1 / t3 := by ring
  have h3 : (1 / t3) * t2 = t2 / t3 := by ring
  rw [h1, h2, h3]
  match_scalars <;> ring

private theorem w6a9_affLt_swap {a b x y : V3}
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
    refine ⟨-(t1 / t3), -(t2 / t3), 1 / t3, div_neg_of_pos_of_neg one_pos ht3, ?_, ?_⟩
    · exact w6a9_div_combo ht3.ne hsum
    · exact w6a9_div_combo_vec ht3.ne hy'
  · rintro ⟨s1, s2, s3, hs3, hsum, hx'⟩
    refine ⟨-(s1 / s3), -(s2 / s3), 1 / s3, div_neg_of_pos_of_neg one_pos hs3, ?_, ?_⟩
    · exact w6a9_div_combo hs3.ne hsum
    · exact w6a9_div_combo_vec hs3.ne hx'

private theorem w6a9_affine_cancel {X Y : V3} {mu lam h c t2 t3 : ℝ}
    (h1 : mu * c + lam * t3 = 0) :
    mu • (h • X + c • Y) + lam • (t2 • X + t3 • Y)
      = (mu * h + lam * t2) • X := by
  have hh : mu • (h • X + c • Y) + lam • (t2 • X + t3 • Y)
      = (mu * h + lam * t2) • X + (mu * c + lam * t3) • Y := by module
  rw [hh, h1, zero_smul, add_zero]

/-- w6a9: LA14 `OPPOSITE_SIDES_IMP_INTER` verbatim copy. -/
private theorem w6a9_opp_sides {va vb vc a b : V3}
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
    rw [hp, e1, haeq', hbeq', w6a9_affine_cancel hkey]
  have haff : p ∈ (affineSpan ℝ ({va, vb} : Set V3) : Set V3) := by
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨mu * h + lam * t2, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hpsub]
    abel
  exact Set.nonempty_iff_ne_empty.mp ⟨p, hconv, haff⟩

/-- w6a9: LA14 `w15_char3` reshaped to take `localFan_p2` directly. -/
private theorem w6a9_char3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf2 : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) (i : ℕ) :
    ¬ Collinear ℝ ({0, (rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3) := by
  have hbase : ¬ Collinear ℝ
      ({0, (rhoNode1 FF)^[i] v, rhoNode1 FF ((rhoNode1 FF)^[i] v)} : Set V3) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf2 (w6a_iter_rho_mem hlf2 hv i)
  have hgoal : (rhoNode1 FF)^[i + 1] v = rhoNode1 FF ((rhoNode1 FF)^[i] v) := by
    rw [show i + 1 = Nat.succ i from rfl, Function.iterate_succ_apply']
  rw [hgoal]
  exact hbase

/-- w6a9: LA14 `SUCCESSIVE_RHO_NODE1_AFF_LT` copy (`ITER_IN_AFF_GT_2_1_p37`
route, LA37). -/
private theorem w6a9_successive {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v : V3} {l : ℕ} {U P : Set V3}
    (hlf : LocalFan V E FF) (hlf2 : localFan_p2 V E FF) (hv : v ∈ V)
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
    (U := U) (P := P) hlf hv hU' hP' h0 hUsub (i - 1) hj
  have e2 : i - 1 + 2 = i + 1 := by omega
  have e1 : i - 1 + 1 = i := by omega
  rw [e2, e1] at hstep
  have hnc1 : ¬ Collinear ℝ
      ({0, (rhoNode1 FF)^[i - 1] v, (rhoNode1 FF)^[i] v} : Set V3) := by
    have hh := w6a9_char3 hlf2 hv (i - 1)
    rwa [show i - 1 + 1 = i from by omega] at hh
  have hnc2 : ¬ Collinear ℝ
      ({0, (rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3) :=
    w6a9_char3 hlf2 hv i
  have hx : (rhoNode1 FF)^[i - 1] v ∉ ({0, (rhoNode1 FF)^[i] v} : Set V3) :=
    w6a9_ncol_mid_notMem hnc1
  have hy : (rhoNode1 FF)^[i + 1] v ∉ ({0, (rhoNode1 FF)^[i] v} : Set V3) :=
    w6a9_ncol_third_notMem hnc2
  exact (w6a9_affLt_swap (x := (rhoNode1 FF)^[i - 1] v)
    (y := (rhoNode1 FF)^[i + 1] v) hx hy).mp hstep

/-- w6a9: LA14 `TWO_SIDES_SUCESSIVE` copy. -/
private theorem w6a9_two_sides {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v : V3} {l : ℕ} {U P : Set V3}
    (hlf : LocalFan V E FF) (hlf2 : localFan_p2 V E FF) (hv : v ∈ V)
    (hU : {(rhoNode1 FF)^[n] v | n ≤ l} = U)
    (hP : plane_p2 P) (h0 : (0 : V3) ∈ P) (hUsub : U ⊆ P) :
    ∀ i, 0 < i → i < l →
      conv0_p2 ({(rhoNode1 FF)^[i - 1] v, (rhoNode1 FF)^[i + 1] v} : Set V3) ∩
        (affineSpan ℝ ({0, (rhoNode1 FF)^[i] v} : Set V3) : Set V3) ≠ ∅ := by
  intro i hi hil
  have hlt := w6a9_successive hlf hlf2 hv hU hP h0 hUsub i hi hil
  have hnc := w6a9_char3 hlf2 hv i
  have hdisj : Disjoint ({0, (rhoNode1 FF)^[i] v} : Set V3)
      ({(rhoNode1 FF)^[i + 1] v} : Set V3) := by
    rw [Set.disjoint_singleton_right]
    exact w6a9_ncol_third_notMem hnc
  have hgt : (rhoNode1 FF)^[i + 1] v ∈
      affGt ({0, (rhoNode1 FF)^[i] v} : Set V3) ({(rhoNode1 FF)^[i + 1] v} : Set V3) :=
    DISJOINT_IMP_Z_IN_AFF_GT hdisj
  have hmemV : (rhoNode1 FF)^[i] v ∈ V := w6a_iter_rho_mem hlf2 hv i
  obtain ⟨-, -, -, -, -, hfan2, -, -⟩ := hlf2
  have hvab : (0 : V3) ≠ (rhoNode1 FF)^[i] v :=
    (FAN_IMP_V_DIFF hfan2 ((rhoNode1 FF)^[i] v) hmemV).symm
  have hint := w6a9_opp_sides (va := 0) (vb := (rhoNode1 FF)^[i] v)
    (vc := (rhoNode1 FF)^[i + 1] v) (a := (rhoNode1 FF)^[i + 1] v)
    (b := (rhoNode1 FF)^[i - 1] v) hvab hdisj hgt hlt
  rw [show ({(rhoNode1 FF)^[i - 1] v, (rhoNode1 FF)^[i + 1] v} : Set V3)
        = ({(rhoNode1 FF)^[i + 1] v, (rhoNode1 FF)^[i - 1] v} : Set V3) by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  exact hint

/-- w6a9: generic fan vertex off the axis plane (LA9
`PROPERTIES_GENERIC_LOCAL_FAN_p9`; `generic_p2` ≡ `Generic`). -/
private theorem w6a9_hncu {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf2 : localFan_p2 V E FF) (hg : Generic V E) (u : V3) (hu : u ∈ V) :
    ∀ t ∈ V, t ≠ u → ¬ Collinear3 0 u t :=
  PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf2 (fun _ _ => trivial) hg u hu

private theorem w6a9_notcirc {V : Set V3} {E : Set (Set V3)} (hg : Generic V E) :
    ¬ Circular V E := by
  intro hc
  obtain ⟨a, b, u, hab, hu, hne⟩ := hc
  have hempty := hg a b u hab hu
  exact hne (Set.eq_empty_iff_forall_notMem.mpr
    fun x hx => by
      have hx2 : x ∈ affGe ({0} : Set V3) ({a, b} : Set V3) ∩
          affLt ({0} : Set V3) ({u} : Set V3) :=
        Set.mem_inter (w6a9_affGt_sub hx.1) hx.2
      rw [hempty] at hx2
      exact hx2)

/-- w6a9: LA14 `w15_clf2` copy with explicit `hedge`. -/
private theorem w6a9_clf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hcopy := hlf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  obtain ⟨-, -, -, -, -, hsub, -⟩ := localFan_data hlf
  have hlf2 := localFan_p2.of_LocalFan_noIso hlf hedge
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

theorem GENERIC_LOCAL_FAN_AZIM_POS {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi)
    (v w : V3) (hv : v ∈ V) (hw : w ∈ V) (hwv : w ≠ v) (hwr : w ≠ rhoNode1 FF v) :
    0 < Real.sin (azim (0 : V3) v (rhoNode1 FF v) w) := by
  -- p2 world and spine facts
  have hlf2 : localFan_p2 V E FF := w6a_to_p2 h.1 hedge
  have hclf2 : convexLocalFan_p2 V E FF := w6a9_clf2 h hedge
  have hlf2c := hlf2
  obtain ⟨-, -, -, -, -, hfan2, -, -⟩ := hlf2c
  have hv0ne : v ≠ 0 := FAN_IMP_V_DIFF hfan2 v hv
  obtain ⟨-, -, -, -, -, h2reg⟩ := h.1
  have hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2 := fun u hu => h2reg u hu
  have hncu := w6a9_hncu hlf2 hg v hv
  have hnotcirc := w6a9_notcirc hg
  have hmem : ∀ n : ℕ, (rhoNode1 FF)^[n] v ∈ V := fun n => w6a_iter_rho_mem hlf2 hv n
  have hdis : ∀ i j : ℕ, i < j → j < V.ncard → (rhoNode1 FF)^[j] v ≠ (rhoNode1 FF)^[i] v :=
    fun i j hij hjk => LOFA_IMP_DIS_ELMS23 hlf2 hv i j hij hjk
  have hid : (rhoNode1 FF)^[V.ncard] v = v := w6a_iter_rho_card hlf2 hv
  -- orbit index of w (stub #4)
  obtain ⟨m, hm, hwm⟩ := LOCAL_FAN_ORBIT_MAP_EXPLICIT_LA7 h.1 hedge v w hv hw
  have hm0 : m ≠ 0 := by
    intro hc
    rw [hc, Function.iterate_zero_apply] at hwm
    exact hwv hwm
  have hm1 : m ≠ 1 := by
    intro hc
    rw [hc, show (1:ℕ) = Nat.succ 0 from rfl, Function.iterate_succ_apply',
      Function.iterate_zero_apply] at hwm
    exact hwr hwm
  have hm2 : 2 ≤ m := by omega
  have hne1' : rhoNode1 FF v ≠ v := hdis 0 1 (by omega) (by omega)
  have hnc1' : ¬ Collinear3 0 v (rhoNode1 FF v) := hncu _ (hmem 1) hne1'
  have hshift : ∀ n : ℕ, (rhoNode1 FF)^[n] ((rhoNode1 FF)^[m] v) = (rhoNode1 FF)^[m + n] v := by
    intro n
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have hrn : ∀ j : ℕ, rhoNode1 FF ((rhoNode1 FF)^[j] v) = (rhoNode1 FF)^[j + 1] v := by
    intro j
    rw [show j + 1 = Nat.succ j from rfl, Function.iterate_succ_apply']
  -- orbit azimuth bounds (LA35 wSectorAt_p35) and monotonicity (LA35 w2OrigMono_p35)
  have hsect : ∀ j : ℕ, 0 ≤ azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[j] v) ∧
      azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[j] v) ≤ Real.pi :=
    fun j => wSectorAt_p35 h hEE2 hv _ (hmem j)
  have hmono : ∀ i j : ℕ, i < j → j < V.ncard →
      azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[i] v) ≤
        azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[j] v) :=
    fun i j hij hjk => w2OrigMono_p35 h hEE2 hv hncu hnotcirc hij hjk
  have hbmw : 0 ≤ azim (0:V3) v (rhoNode1 FF v) w ∧
      azim (0:V3) v (rhoNode1 FF v) w ≤ Real.pi := by
    have hb := hsect m
    rw [← hwm] at hb
    exact hb
  -- the reference azimuth at the reference ray itself is 0
  have hbta_self : azim (0:V3) v (rhoNode1 FF v) (rhoNode1 FF v) = 0 := by
    rw [azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := v) (w := rhoNode1 FF v)
      (x := rhoNode1 FF v) hnc1' hnc1']
    exact (affGt_pair_iff (v0 := (0:V3)) (v1 := v) (x := rhoNode1 FF v)
      (y := rhoNode1 FF v) (Ne.symm hv0ne) (FAN_IMP_V_DIFF hfan2 _ (hmem 1)) hne1').mpr
      ⟨1, one_pos, 0, by simp⟩
  -- GT-bridge into the window plane
  have hgtsub0 : ∀ x : V3, x ∈ affGt ({0, v} : Set V3) ({rhoNode1 FF v} : Set V3) →
      x ∈ (affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3) : Set V3) := by
    intro x hx
    have h1 := AFF_GT_SUBSET_AFFINE_HULL ({0, v} : Set V3) ({rhoNode1 FF v} : Set V3) hx
    rwa [show (({0, v} : Set V3) ∪ ({rhoNode1 FF v} : Set V3))
          = ({(0:V3), v, rhoNode1 FF v} : Set V3) from by
        ext z; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h1
  -- window in the plane {0, v, ρv}: interior orbit vertex ρv is flat (angle π)
  have hne_zero : azim (0:V3) v (rhoNode1 FF v) w ≠ 0 := by
    intro hz
    have hbm : azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[m] v) = 0 := by
      rw [← hwm]; exact hz
    have hbta0 : ∀ j : ℕ, 2 ≤ j → j ≤ m →
        azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[j] v) = 0 := by
      intro j hj2 hjm
      rcases Nat.eq_or_lt_of_le hjm with rfl | hjlt
      · exact hbm
      · have hle := hmono j m hjlt hm
        rw [hbm] at hle
        exact le_antisymm hle (hsect j).1
    have hnc0 : ¬ Collinear ℝ ({0, v, rhoNode1 FF v} : Set V3) := hncu _ (hmem 1) hne1'
    have hplane0 : plane_p2 (affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3)) :=
      ⟨0, v, rhoNode1 FF v, hnc0, rfl⟩
    have h0P0 : (0:V3) ∈ (affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3) : Set V3) :=
      mem_affineSpan ℝ (by simp)
    have hUsub0 : ({(rhoNode1 FF)^[n] v | n ≤ m} : Set V3) ⊆
        (affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3) : Set V3) := by
      rintro z ⟨n, hn, rfl⟩
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [show (n:ℕ) = 0 from by omega, Function.iterate_zero_apply]
        exact mem_affineSpan ℝ (by simp)
      · have hb0 : azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[n] v) = 0 := by
          rcases Nat.lt_or_ge n 2 with h2 | h2
          · rw [show (n:ℕ) = 1 from by omega]; exact hbta_self
          · exact hbta0 n h2 (by omega)
        exact hgtsub0 _ ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := v)
          (w := rhoNode1 FF v) (x := (rhoNode1 FF)^[n] v) hnc1'
          (hncu _ (hmem n) (hdis 0 n h0 (by omega)))).mp hb0)
    have htwo0 := w6a9_two_sides h.1 hlf2 hv rfl hplane0 h0P0 hUsub0 1 (by omega) (by omega)
    rw [show ((rhoNode1 FF)^[1 - 1] v) = v from by simp,
        show ((rhoNode1 FF)^[1 + 1] v) = ((rhoNode1 FF)^[2] v) from by simp,
        show ((rhoNode1 FF)^[1] v) = rhoNode1 FF v from by simp] at htwo0
    have hempty0 : ({(rhoNode1 FF)^[2] v, v} : Set V3) ∩
        ↑(line[ℝ, (0:V3), rhoNode1 FF v]) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1
      rcases hx1 with hx1 | hx1
      · rw [hx1] at hx2
        refine w6a9_char3 hlf2 hv 1 ?_
        have hx3 : ((rhoNode1 FF)^[2] v) ∈
            (affineSpan ℝ ({(0:V3), rhoNode1 FF v} : Set V3) : Set V3) := by
          rw [show (line[ℝ, (0:V3), rhoNode1 FF v] : Set V3)
                = (affineSpan ℝ ({(0:V3), rhoNode1 FF v} : Set V3)) from rfl] at hx2
          exact hx2
        exact collinear_triple_iff.mpr (Or.inl hx3)
      · rw [hx1] at hx2
        have hx3 : v ∈ (affineSpan ℝ ({(0:V3), rhoNode1 FF v} : Set V3) : Set V3) := by
          rw [show (line[ℝ, (0:V3), rhoNode1 FF v] : Set V3)
                = (affineSpan ℝ ({(0:V3), rhoNode1 FF v} : Set V3)) from rfl] at hx2
          exact hx2
        have hncm0 : ¬ Collinear ℝ ({0, v, rhoNode1 FF v} : Set V3) := hncu _ (hmem 1) hne1'
        have hswap : ({0, v, rhoNode1 FF v} : Set V3)
            = ({0, rhoNode1 FF v, v} : Set V3) := by
          ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hswap] at hncm0
        exact hncm0 (collinear_triple_iff.mpr (Or.inl hx3))
    have hne0 : ¬ (↑(line[ℝ, rhoNode1 FF v, (0:V3)]) ∩
        conv0_p2 ({v, (rhoNode1 FF)^[2] v} : Set V3)) = ∅ := by
      intro hE
      refine htwo0 ?_
      rw [Set.inter_comm] at hE
      rw [show (({rhoNode1 FF v, (0:V3)} : Set V3) : Set V3)
            = ({0, rhoNode1 FF v} : Set V3) from by
          ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hE
      exact hE
    have hoz0sub : ({(rhoNode1 FF)^[2] v, rhoNode1 FF v, v} : Set V3) ⊆ V := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hmem 2
      · exact hmem 1
      · exact hv
    have hoz0sub2 : ({(0:V3), (rhoNode1 FF)^[2] v, rhoNode1 FF v, v} : Set V3) ⊆
        (affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3) : Set V3) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h0P0
      · exact hgtsub0 _ ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := v)
          (w := rhoNode1 FF v) (x := (rhoNode1 FF)^[2] v) hnc1'
          (hncu _ (hmem 2) (hdis 0 2 (by omega) (by omega)))).mp (hbta0 2 (by omega) (by omega)))
      · exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
    have hoz0 := OZQVSFF hclf2 (u := (rhoNode1 FF)^[2] v) (v := rhoNode1 FF v)
      (w := v) (P := affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3))
      hoz0sub hplane0 hoz0sub2 hempty0 hne0
    have hcontr := hia (rhoNode1 FF v) (hmem 1)
    rw [show interiorAngle1 (0:V3) FF (rhoNode1 FF v) = Real.pi from hoz0.1] at hcontr
    exact lt_irrefl _ hcontr
  -- upper exclusion: azimuth π is impossible at w
  have hne_pi : azim (0:V3) v (rhoNode1 FF v) w ≠ Real.pi := by
    intro hpi
    have hbm : azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[m] v) = Real.pi := by
      rw [← hwm]; exact hpi
    rcases Nat.lt_or_ge m (V.ncard - 1) with hmlt | hmeq
    · -- m < k-1: suffix window at ρ^m v; the vertex ρ^(m+1) v goes flat
      have hm1lt : m + 1 < V.ncard := by omega
      have hle := hmono m (m + 1) (by omega) hm1lt
      rw [hbm] at hle
      have hbm1 : azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[m + 1] v) = Real.pi :=
        le_antisymm (hsect (m + 1)).2 hle
      have hncm : ¬ Collinear ℝ ({0, v, (rhoNode1 FF)^[m] v} : Set V3) :=
        hncu _ (hmem m) (hdis 0 m (by omega) hm)
      have hUsub : ∀ j : ℕ, m ≤ j → j < V.ncard →
          (rhoNode1 FF)^[j] v ∈ affGt ({0, v} : Set V3) ({(rhoNode1 FF)^[m] v} : Set V3) := by
        intro j hjm hjk
        have hbmj : azim (0:V3) v (rhoNode1 FF v) ((rhoNode1 FF)^[j] v) = Real.pi := by
          rcases Nat.eq_or_lt_of_le hjm with rfl | hjlt
          · exact hbm
          · have hjle := hmono m j hjlt hjk
            rw [hbm] at hjle
            exact le_antisymm (hsect j).2 hjle
        exact (azim_eq_azim_iff (v0 := (0:V3)) (v1 := v) (w := rhoNode1 FF v)
          (x := (rhoNode1 FF)^[m] v) (y := (rhoNode1 FF)^[j] v) hnc1'
          (hncu _ (hmem m) (hdis 0 m (by omega) hm))
          (hncu _ (hmem j) (hdis 0 j (by omega) hjk))).mp (by rw [hbmj, hbm])
      have hgtsub : ∀ x : V3, x ∈ affGt ({0, v} : Set V3) ({(rhoNode1 FF)^[m] v} : Set V3) →
          x ∈ (affineSpan ℝ ({(0:V3), v, (rhoNode1 FF)^[m] v} : Set V3) : Set V3) := by
        intro x hx
        have h1 := AFF_GT_SUBSET_AFFINE_HULL ({0, v} : Set V3) ({(rhoNode1 FF)^[m] v} : Set V3) hx
        rwa [show (({0, v} : Set V3) ∪ ({(rhoNode1 FF)^[m] v} : Set V3))
              = ({(0:V3), v, (rhoNode1 FF)^[m] v} : Set V3) from by
            ext z; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h1
      have hplane : plane_p2 (affineSpan ℝ ({(0:V3), v, (rhoNode1 FF)^[m] v} : Set V3)) :=
        ⟨0, v, (rhoNode1 FF)^[m] v, hncm, rfl⟩
      have h0Pw : (0:V3) ∈ (affineSpan ℝ ({(0:V3), v, (rhoNode1 FF)^[m] v} : Set V3) : Set V3) :=
        mem_affineSpan ℝ (by simp)
      have hUsub2 : ({(rhoNode1 FF)^[n] ((rhoNode1 FF)^[m] v) | n ≤ V.ncard - m} : Set V3) ⊆
          (affineSpan ℝ ({(0:V3), v, (rhoNode1 FF)^[m] v} : Set V3) : Set V3) := by
        rintro z ⟨n, hn, rfl⟩
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · rw [show (n:ℕ) = 0 from by omega, Function.iterate_zero_apply]
          exact mem_affineSpan ℝ (by simp)
        · rw [hshift n]
          rcases Nat.lt_or_ge (m + n) V.ncard with hlt | hge
          · exact hgtsub _ (hUsub (m + n) (by omega) hlt)
          · rw [show (m:ℕ) + n = V.ncard from by omega, hid]
            exact mem_affineSpan ℝ (by simp)
      have htwo := w6a9_two_sides h.1 hlf2 (hmem m) rfl hplane h0Pw hUsub2 1 (by omega)
        (by omega)
      have hn2 : ((rhoNode1 FF)^[2] ((rhoNode1 FF)^[m] v)) = ((rhoNode1 FF)^[m + 2] v) := by
        rw [← Function.iterate_add_apply, Nat.add_comm]
      have hn1 : ((rhoNode1 FF)^[1] ((rhoNode1 FF)^[m] v)) = ((rhoNode1 FF)^[m + 1] v) := by
        rw [← Function.iterate_add_apply, Nat.add_comm]
      rw [show ((rhoNode1 FF)^[0] ((rhoNode1 FF)^[m] v)) = ((rhoNode1 FF)^[m] v) from by simp,
        hn2, hn1] at htwo
      have hempty : ({(rhoNode1 FF)^[m + 2] v, (rhoNode1 FF)^[m] v} : Set V3) ∩
          ↑(line[ℝ, (0:V3), (rhoNode1 FF)^[m + 1] v]) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1
        rcases hx1 with hx1 | hx1
        · rw [hx1] at hx2
          refine w6a9_char3 hlf2 (hmem m) 1 ?_
          have hmsucc : ((rhoNode1 FF)^[m + 1] v) = rhoNode1 FF ((rhoNode1 FF)^[m] v) := by
            rw [show ((m:ℕ) + 1 = Nat.succ m) from rfl, Function.iterate_succ_apply']
          have hm2app : ((rhoNode1 FF)^[m + 2] v) = rhoNode1 FF ((rhoNode1 FF)^[m + 1] v) := by
            rw [show ((m:ℕ) + 2 = Nat.succ (m + 1)) from rfl, Function.iterate_succ_apply']
          have hx3 : ((rhoNode1 FF)^[1 + 1] ((rhoNode1 FF)^[m] v)) ∈
              (line[ℝ, (0:V3), (rhoNode1 FF)^[1] ((rhoNode1 FF)^[m] v)] : Set V3) := by
            have hx4 : ((rhoNode1 FF)^[m + 2] v) ∈
                (affineSpan ℝ ({(0:V3), (rhoNode1 FF)^[m + 1] v} : Set V3) : Set V3) := by
              rw [show (line[ℝ, (0:V3), (rhoNode1 FF)^[m + 1] v] : Set V3)
                    = (affineSpan ℝ ({(0:V3), (rhoNode1 FF)^[m + 1] v} : Set V3)) from rfl] at hx2
              exact hx2
            rw [hm2app, hmsucc] at hx4
            exact hx4
          exact collinear_triple_iff.mpr (Or.inl hx3)
        · rw [hx1] at hx2
          have hx3 : ((rhoNode1 FF)^[m] v) ∈
              (affineSpan ℝ ({(0:V3), (rhoNode1 FF)^[m + 1] v} : Set V3) : Set V3) := by
            rw [show (line[ℝ, (0:V3), (rhoNode1 FF)^[m + 1] v] : Set V3)
                  = (affineSpan ℝ ({(0:V3), (rhoNode1 FF)^[m + 1] v} : Set V3)) from rfl] at hx2
            exact hx2
          have hncm0 : ¬ Collinear ℝ
              ({0, (rhoNode1 FF)^[m] v, (rhoNode1 FF)^[m + 1] v} : Set V3) := by
            have hncm0' := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf2 (hmem m)
            rw [show rhoNode1_p2 FF ((rhoNode1 FF)^[m] v)
                  = rhoNode1 FF ((rhoNode1 FF)^[m] v) from rfl, hrn m] at hncm0'
            exact hncm0'
          have hswap : ({0, (rhoNode1 FF)^[m] v, (rhoNode1 FF)^[m + 1] v} : Set V3)
              = ({0, (rhoNode1 FF)^[m + 1] v, (rhoNode1 FF)^[m] v} : Set V3) := by
            ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
          rw [hswap] at hncm0
          exact hncm0 (collinear_triple_iff.mpr (Or.inl hx3))
      have hne : ¬ (↑(line[ℝ, (rhoNode1 FF)^[m + 1] v, (0:V3)]) ∩
          conv0_p2 ({(rhoNode1 FF)^[m] v, (rhoNode1 FF)^[m + 2] v} : Set V3)) = ∅ := by
        intro hE
        refine htwo ?_
        rw [Set.inter_comm] at hE
        rw [show (({(rhoNode1 FF)^[m + 1] v, (0:V3)} : Set V3)
              = ({(0:V3), (rhoNode1 FF)^[m + 1] v} : Set V3)) from by
            ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hE
        exact hE
      have hsub2 : ({(0:V3), (rhoNode1 FF)^[m + 2] v, (rhoNode1 FF)^[m + 1] v,
          (rhoNode1 FF)^[m] v} : Set V3) ⊆
          (affineSpan ℝ ({(0:V3), v, (rhoNode1 FF)^[m] v} : Set V3) : Set V3) := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact h0Pw
        · rcases Nat.lt_or_ge (m + 2) V.ncard with hlt | hge
          · exact hgtsub _ (hUsub (m + 2) (by omega) hlt)
          · rw [show (m:ℕ) + 2 = V.ncard from by omega, hid]
            exact mem_affineSpan ℝ (by simp)
        · exact hgtsub _ (hUsub (m + 1) (by omega) hm1lt)
        · exact mem_affineSpan ℝ (by simp)
      have hozsub : ({(rhoNode1 FF)^[m + 2] v, (rhoNode1 FF)^[m + 1] v,
          (rhoNode1 FF)^[m] v} : Set V3) ⊆ V := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact hmem (m + 2)
        · exact hmem (m + 1)
        · exact hmem m
      have hoz := OZQVSFF hclf2 (u := (rhoNode1 FF)^[m + 2] v) (v := (rhoNode1 FF)^[m + 1] v)
        (w := (rhoNode1 FF)^[m] v) (P := affineSpan ℝ ({(0:V3), v, (rhoNode1 FF)^[m] v} : Set V3))
        hozsub hplane hsub2 hempty hne
      have hcontr := hia ((rhoNode1 FF)^[m + 1] v) (hmem (m + 1))
      rw [show interiorAngle1 (0:V3) FF ((rhoNode1 FF)^[m + 1] v) = Real.pi from hoz.1] at hcontr
      exact lt_irrefl _ hcontr
    · -- m = k-1: w = ιv, and the angle at v equals that azimuth
      have hme : m = V.ncard - 1 := by omega
      have hivs : ivsRhoNode1 FF v = (rhoNode1 FF)^[V.ncard - 1] v := w6a_ivs_eq_rho_pred hlf2 hv
      have hia_eq : interiorAngle1 (0:V3) FF v = azim (0:V3) v (rhoNode1 FF v) w := by
        show azim (0:V3) v (rhoNode1 FF v) (ivsRhoNode1 FF v) = _
        rw [hivs, hwm, hme]
      have hcontr := hia v hv
      rw [hia_eq, hpi] at hcontr
      exact lt_irrefl _ hcontr
  refine Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hbmw.1 (Ne.symm hne_zero)) ?_
  exact lt_of_le_of_ne hbmw.2 hne_pi

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
  obtain ⟨hfan, x, hx, hFF, -, -⟩ := h
  intro h0
  have hx' : x ∈ FF := by rw [hFF]; exact mem_orbitMap_self _ x
  rw [h0] at hx'
  exact absurd hx' (by simp)

/-- HOL `LOCAL_FAN_NOT_CARD_FF_GE_2` (polar_fan.hl:521). -/
theorem LOCAL_FAN_NOT_CARD_FF_GE_2 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) : 2 ≤ FF.ncard := by
  obtain ⟨hfan, x, hx, hFF, hD, -⟩ := h
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

/-! ### W11b2p fan7 kit (`p11w_*`; WSEWPCH wave W11b2p)

Support pieces for closing the fan7-equivalence stubs:
`affGe {x} ∅ = {x}`, the graph-edge set trichotomy, and right-monotonicity of
`affGe` (HOL `AFF_GE_MONO_RIGHT` — no definition in the reference tree, newly
proved from the `Affsign` semantics). -/

section W11b2pKit

/-- `affGe {x} ∅ = {x}`：空方向的闭锥退化为基点（`Affsign` 系数只能落在 `x`
且和为 1）。 -/
theorem P11W_AFFGE_EMPTY (x : V3) : affGe ({x} : Set V3) (∅ : Set V3) = {x} := by
  ext z
  constructor
  · intro hz
    simp only [affGe, Set.mem_setOf_eq, Affsign] at hz
    obtain ⟨f, hfin, hv, -, hone⟩ := hz
    have h1 : hfin.toFinset = ({(x : V3)} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset]
    rw [h1, Finset.sum_singleton] at hv hone
    rw [hv, hone, one_smul]
    exact Set.mem_singleton x
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hfin : ({(x : V3)} ∪ (∅ : Set V3)).Finite :=
      (Set.finite_singleton x).union Set.finite_empty
    have htof : hfin.toFinset = ({(x : V3)} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset]
    refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
    · rw [htof, Finset.sum_singleton]
      simp only [one_smul]
    · intro w hw
      simp at hw
    · rw [htof, Finset.sum_singleton]

/-- `affGe` 右单调性的**单点支撑形**（HOL `AFF_GE_MONO_RIGHT` 在
`GMLWKPK_ALT` 消费处的按需形；reference 无定义，按 `Affsign` 语义新证）。
s = {x} 且 x ∉ t' 时系数零扩展直接成立（这正是 hx 前提的用途：x 不进 t'，
不受新签约束）。一般 s 形为假（s-自由系数遇 t'-新点），不立。 -/
theorem P11W_AFFGE_MONO_SINGLE {x : V3} {t t' : Set V3} (hsub : t ⊆ t')
    (hx : x ∉ t') (ht' : t'.Finite) :
    affGe ({x} : Set V3) t ⊆ affGe ({x} : Set V3) t' := by
  intro v hv
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hv ⊢
  obtain ⟨f, hfin, hvec, hsign, hone⟩ := hv
  have hfin' : ({x} ∪ t').Finite := (Set.finite_singleton x).union ht'
  have hsubF : hfin.toFinset ⊆ hfin'.toFinset := by
    intro w hw
    exact (Set.Finite.mem_toFinset hfin').mpr (by
      have hw' := (Set.Finite.mem_toFinset hfin).mp hw
      simp only [Set.mem_union, Set.mem_singleton_iff] at hw' ⊢
      rcases hw' with h | h
      · exact Or.inl h
      · exact Or.inr (hsub h))
  have hzeroS : ∀ w ∈ hfin'.toFinset, w ∉ hfin.toFinset →
      (if w ∈ hfin.toFinset then f w else 0) = 0 :=
    fun w _ hw => if_neg hw
  have hzeroV : ∀ w ∈ hfin'.toFinset, w ∉ hfin.toFinset →
      (if w ∈ hfin.toFinset then f w else 0) • w = 0 := by
    intro w _ hw
    rw [if_neg hw, zero_smul]
  refine ⟨fun w => if w ∈ hfin.toFinset then f w else 0, hfin', ?_, ?_, ?_⟩
  · rw [hvec]
    refine Eq.trans (Finset.sum_congr rfl fun w hw => ?_)
      (Finset.sum_subset hsubF hzeroV)
    show f w • w = (if w ∈ hfin.toFinset then f w else 0) • w
    rw [if_pos hw]
  · intro w hw'
    show (0:ℝ) ≤ (if w ∈ hfin.toFinset then f w else 0)
    by_cases hwF : w ∈ hfin.toFinset
    · rw [if_pos hwF]
      have hwt : w ∈ t := by
        have hw's := (Set.Finite.mem_toFinset hfin).mp hwF
        simp only [Set.mem_union, Set.mem_singleton_iff] at hw's
        rcases hw's with h | h
        · exact absurd (h ▸ hw') hx
        · exact h
      exact hsign w hwt
    · rw [if_neg hwF]
  · rw [← hone]
    refine Eq.trans (Finset.sum_subset hsubF hzeroS).symm ?_
    exact Finset.sum_congr rfl fun w hw => if_pos hw

/-- 单点像的两种渲染等价（`image (fun v => {v}) V` = `{s | ∃ v ∈ V, s = {v}}`；
`Eq` 方向不同故非 rfl）。 -/
theorem p11w_img_singleton_eq (V : Set V3) :
    (Set.image (fun v : V3 => ({v} : Set V3)) V)
      = {s : Set V3 | ∃ v ∈ V, s = ({v} : Set V3)} := by
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- 图边三元组：`e1, e2 ∈ E ∪ 单点集`、`Graph E` ⟹ 二者相等、交空或交为单点。 -/
private theorem p11w_edge_trichotomy {E : Set (Set V3)} (hg : Graph E)
    {V : Set V3} {e1 e2 : Set V3}
    (h1 : e1 ∈ E ∪ (image (fun v : V3 => {v}) V))
    (h2 : e2 ∈ E ∪ (image (fun v : V3 => {v}) V)) :
    e1 = e2 ∨ e1 ∩ e2 = ∅ ∨ ∃ v : V3, e1 ∩ e2 = {v} := by
  have hle : ∀ e ∈ E ∪ (image (fun v : V3 => {v}) V), e.Finite ∧ e.ncard ≤ 2 := by
    intro e he
    simp only [Set.mem_union] at he
    rcases he with heE | hes
    · obtain ⟨hfin, hcard⟩ := hg e heE
      refine ⟨hfin, ?_⟩
      rw [Set.ncard_eq_toFinset_card e hfin, hcard]
    · obtain ⟨v, -, rfl⟩ := hes
      exact ⟨Set.finite_singleton v, by simp⟩
  obtain ⟨h1fin, h1le⟩ := hle e1 h1
  obtain ⟨h2fin, h2le⟩ := hle e2 h2
  have hIle : (e1 ∩ e2).ncard ≤ 2 :=
    le_trans (Set.ncard_le_ncard Set.inter_subset_left h1fin) h1le
  have hfinI : (e1 ∩ e2).Finite := h1fin.subset Set.inter_subset_left
  rcases Nat.lt_or_ge (e1 ∩ e2).ncard 1 with h0 | h1'
  · right
    have h0' : (e1 ∩ e2).ncard = 0 := by omega
    exact Or.inl ((Set.ncard_eq_zero hfinI).mp h0')
  · rcases Nat.lt_or_ge (e1 ∩ e2).ncard 2 with hlt | hge
    · right
      have h1'' : (e1 ∩ e2).ncard = 1 := by omega
      obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1''
      exact Or.inr ⟨v, hv⟩
    · left
      have h2' : (e1 ∩ e2).ncard = 2 := le_antisymm hIle hge
      have he1eq : e1 ∩ e2 = e1 :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_left
          (by rw [h2']; exact h1le) h1fin
      have he2eq : e1 ∩ e2 = e2 :=
        Set.eq_of_subset_of_ncard_le Set.inter_subset_right
          (by rw [h2']; exact h2le) h2fin
      rw [← he1eq, he2eq]

end W11b2pKit

/-! ## fan7 / FAN equivalences (polar_fan.hl:572-1047) -/

/-- HOL `GMLWKPK` (polar_fan.hl:572). -/
theorem GMLWKPK (x : V3) (V : Set V3) (E : Set (Set V3)) (hg : Graph E) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
          (∀ v : V3, e1 ∩ e2 = {v} → affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v}) := by
  constructor
  · intro h7 e1 he1 e2 he2
    rw [p11w_img_singleton_eq] at he1 he2
    have h := h7 e1 he1 e2 he2
    refine ⟨fun h0 => ?_, fun v hv => ?_⟩
    · rw [h, h0]
      exact P11W_AFFGE_EMPTY x
    · rw [h, hv]
  · intro hs e1 he1 e2 he2
    have he1i : e1 ∈ E ∪ (image (fun v : V3 => ({v} : Set V3)) V) := by
      simpa [p11w_img_singleton_eq] using he1
    have he2i : e2 ∈ E ∪ (image (fun v : V3 => ({v} : Set V3)) V) := by
      simpa [p11w_img_singleton_eq] using he2
    rcases p11w_edge_trichotomy (V := V) hg he1i he2i with heq | hemp | ⟨v, hv⟩
    · rw [heq, Set.inter_self, Set.inter_self]
    · rw [hemp, P11W_AFFGE_EMPTY x]
      exact (hs e1 he1i e2 he2i).1 hemp
    · rw [hv]
      exact (hs e1 he1i e2 he2i).2 v hv

/-- HOL `GMLWKPK_ALT` (polar_fan.hl:608). -/
theorem GMLWKPK_ALT (x : V3) (V : Set V3) (E : Set (Set V3)) (hg : Graph E)
    (hx : ∀ e ∈ E, x ∉ e) :
    (fan7 x V E ↔
      (∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
      (∀ e1 ∈ E, ∀ e2 ∈ E, ∀ v : V3, e1 ∩ e2 = {v} →
        affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v})) := by
  constructor
  · intro h7
    have hs := (GMLWKPK x V E hg).mp h7
    refine ⟨fun e1 he1 e2 he2 => (hs e1 he1 e2 he2).1, ?_⟩
    intro e1 he1 e2 he2 v hv
    exact (hs e1 (Set.mem_union_left _ he1) e2 (Set.mem_union_left _ he2)).2 v hv
  · rintro ⟨h1, h2⟩
    refine (GMLWKPK x V E hg).mpr ?_
    intro e1 he1 e2 he2
    refine ⟨h1 e1 he1 e2 he2, fun v hv => ?_⟩
    simp only [Set.mem_union] at he1
    rcases he1 with he1E | he1s
    · have he2' := he2
      simp only [Set.mem_union] at he2'
      rcases he2' with he2E | he2s
      · exact h2 e1 he1E e2 he2E v hv
      · -- e2 单点
        obtain ⟨b, -, rfl⟩ := he2s
        have hve : v ∈ e1 ∩ ({b} : Set V3) := by
          rw [hv]
          exact Set.mem_singleton v
        have hve' := hve
        simp only [Set.mem_inter_iff] at hve'
        obtain ⟨hve1, hvs⟩ := hve'
        have hvb : v = b := Set.mem_singleton_iff.mp hvs
        rw [hvb]
        exact Set.inter_eq_right.mpr
          (P11W_AFFGE_MONO_SINGLE (x := x) (t := ({b} : Set V3)) (t' := e1) (by
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            rw [← hvb]
            exact hve1) (hx e1 he1E) (hg e1 he1E).1)
    · -- e1 单点
      obtain ⟨a, -, rfl⟩ := he1s
      simp only [Set.mem_union] at he2
      rcases he2 with he2E | he2s
      · have hve : v ∈ ({a} : Set V3) ∩ e2 := by
          rw [hv]
          exact Set.mem_singleton v
        have hve' := hve
        simp only [Set.mem_inter_iff] at hve'
        obtain ⟨hvs, hve2⟩ := hve'
        have hva : v = a := Set.mem_singleton_iff.mp hvs
        rw [hva]
        rw [Set.inter_comm]
        exact Set.inter_eq_right.mpr
          (P11W_AFFGE_MONO_SINGLE (x := x) (t := ({a} : Set V3)) (t' := e2) (by
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            rw [← hva]
            exact hve2) (hx e2 he2E) (hg e2 he2E).1)
      · obtain ⟨b, -, rfl⟩ := he2s
        have hve : v ∈ ({a} : Set V3) ∩ {b} := by
          rw [hv]
          exact Set.mem_singleton v
        have hve' := hve
        simp only [Set.mem_inter_iff] at hve'
        obtain ⟨hvs, hvs2⟩ := hve'
        have hva : v = a := Set.mem_singleton_iff.mp hvs
        have hvb : v = b := Set.mem_singleton_iff.mp hvs2
        rw [← hva, ← hvb, Set.inter_self]

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

/-! ### W11b2p2 fan7 closure (`p11w2_*`; WSEWPCH wave W11b2p2)

Closes the remaining fan7 stubs by a **coefficient-form** route instead of
the x-anchored wedge decompositions of HOL `AFF_GE_AFF_GT_DECOMP`.

Truth-check (per the W11b2p discipline, performed before proving):
* the 0-anchored decompositions `aff_ge {0} {u}` / `aff_ge {0} {u,v}` are
  TRUE equalities (the `{0}` coefficient is free and absorbs the sum-1
  constraint); the x-anchored boundary forms need the `u = x` degenerate
  case.  Both families already exist in-tree outside this file
  (`AFF_GE_1_1_0_p17`/`AFF_GE_1_2_0_p17` in `LocalAuto17`,
  `AFF_GE_TO_AFF_GT2_GE1` = HOL `lemma2` in `LocalAuto3`), so duplicating
  them here adds nothing.
* the decisive piece for `FAN7_AFF_GT_CONDITION` is instead the
  **membership coefficient form**: `mem_affGe_singleton(_pair)`
  (`TopologyFan`) rewritten in difference-vector shape; the two-edge cases
  expand `affGe {x} {u,v}` by `AFF_GE_TO_AFF_GT2_GE1` and kill the nine
  intersection terms by `hve`/`hvs`/`hee` or the degenerate `t = x`.

`reference/flyspeck/`: `AFF_GE_AFF_GT_DECOMP` has **no definition** (only
consumption at `polar_fan.hl:675/689`); everything below is newly proved
from the `Affsign` semantics. -/

section W11b2p2Kit

/-- `affGe {x} {v}` 的射线形（`mem_affGe_singleton` 的差向量重写）。 -/
theorem P11W2_GE_SINGLE_REL {x v y : V3} (hxv : x ≠ v) :
    y ∈ affGe {x} {v} ↔ ∃ a : ℝ, 0 ≤ a ∧ y - x = a • (v - x) := by
  constructor
  · intro hy
    obtain ⟨t1, t2, ht2, hsum, hy'⟩ :=
      (mem_affGe_singleton (x := x) (v := v) hxv).mp hy
    refine ⟨t2, ht2, ?_⟩
    have ht1 : t1 = 1 - t2 := by linarith
    rw [hy', ht1]
    module
  · rintro ⟨a, ha, hy⟩
    refine (mem_affGe_singleton (x := x) (v := v) hxv).mpr
      ⟨1 - a, a, ha, by ring, ?_⟩
    have h1 : y = (y - x) + x := by abel
    rw [h1, hy]
    module

/-- `affGe {x} {u,v}` 的差向量系数形（`mem_affGe_singleton_pair` 的重写；
`LocalAuto17` `w_xrq17_mem_affGe_pair_trans` 的同型重建）。 -/
theorem P11W2_GE_PAIR_REL {x u v y : V3}
    (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v) :
    y ∈ affGe {x} {u, v} ↔
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ y - x = a • (u - x) + b • (v - x) := by
  have hdisj : Disjoint ({x} : Set V3) {u, v} := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rcases Set.mem_insert_iff.mp hz' with h | h
    · exact hxu h
    · rw [Set.mem_singleton_iff] at h
      exact hxv h
  constructor
  · intro hy
    obtain ⟨t1, t2, t3, ht2, ht3, hsum, hy'⟩ :=
      (mem_affGe_singleton_pair (x := x) (v := u) (w := v) hdisj huv).mp hy
    have ht1 : t1 = 1 - t2 - t3 := by linarith
    refine ⟨t2, t3, ht2, ht3, ?_⟩
    rw [hy', ht1]
    module
  · rintro ⟨a, b, ha, hb, hy⟩
    refine (mem_affGe_singleton_pair (x := x) (v := u) (w := v) hdisj huv).mpr
      ⟨1 - a - b, a, b, ha, hb, by ring, ?_⟩
    have h1 : y = (y - x) + x := by abel
    rw [h1, hy]
    module

/-- 差向量系数形（严格正）→ `affGt {x} {v}`。 -/
theorem P11W2_GT_SINGLE_REL {x v y : V3} (hxv : x ≠ v) {a : ℝ} (ha : 0 < a)
    (hy : y - x = a • (v - x)) : y ∈ affGt {x} {v} := by
  have hfin : ({x} ∪ {v} : Set V3).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton v)
  have htof : hfin.toFinset = ({x, v} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun z => if z = v then a else 1 - a, hfin, ?_, ?_, ?_⟩
  · rw [htof, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
    show y = (if x = v then a else 1 - a) • x + (if v = v then a else 1 - a) • v
    rw [if_neg hxv, if_pos rfl]
    have h1 : y = (y - x) + x := by abel
    rw [h1, hy]
    module
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simpa using ha
  · rw [htof, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
    show (if x = v then a else 1 - a) + (if v = v then a else 1 - a) = 1
    rw [if_neg hxv, if_pos rfl]
    ring

/-- 差向量系数形（严格正）→ `affGt {x} {u,v}`（`Affsign.of_triple`）。 -/
theorem P11W2_GT_PAIR_REL {x u v y : V3}
    (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hy : y - x = a • (u - x) + b • (v - x)) :
    y ∈ affGt {x} {u, v} := by
  have hy' : y = (1 - a - b) • x + a • u + b • v := by
    have h1 : y = (y - x) + x := by abel
    rw [h1, hy]
    module
  exact Affsign.of_triple (sgn := fun r => 0 < r) a b ha hb hy' hxu hxv huv

/-- 图边两点分解。 -/
theorem P11W2_EDGE_PAIR {E : Set (Set V3)} (hg : Graph E)
    {e : Set V3} (he : e ∈ E) : ∃ a b : V3, a ≠ b ∧ e = {a, b} := by
  obtain ⟨hf, hc⟩ := hg e he
  have h2 : e.ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card e hf, hc]
  obtain ⟨a, b, hab, heq⟩ := Set.ncard_eq_two.mp h2
  exact ⟨a, b, hab, heq⟩

/-- 过给定点的图边分解。 -/
theorem P11W2_EDGE_PAIR_OF_MEM {E : Set (Set V3)} (hg : Graph E)
    {e : Set V3} (he : e ∈ E) {v : V3} (hv : v ∈ e) :
    ∃ u : V3, u ≠ v ∧ e = {u, v} := by
  obtain ⟨a, b, hab, heq⟩ := P11W2_EDGE_PAIR hg he
  subst heq
  rcases Set.mem_insert_iff.mp hv with h | h
  · refine ⟨b, ?_, ?_⟩
    · rw [h]; exact hab.symm
    · rw [h, Set.pair_comm]
  · rw [Set.mem_singleton_iff] at h
    refine ⟨a, ?_, ?_⟩
    · rw [h]; exact hab
    · rw [h]

/-- 基点属于每个 `affGe {x} e`（`x ∉ e`）。 -/
theorem p11w2_mem_self_affGe {x : V3} {e : Set V3}
    (hfin : ({x} ∪ e).Finite) (hx : x ∉ e) : x ∈ affGe {x} e := by
  have hxmem : x ∈ hfin.toFinset :=
    (Set.Finite.mem_toFinset hfin).mpr (Set.mem_union_left e (Set.mem_singleton x))
  have hval_v : ∑ w ∈ hfin.toFinset, (fun z => if z = x then (1 : ℝ) else 0) w • w = x := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hbx
      simp [hbx]
    · intro hxnot
      exact absurd hxmem hxnot
  have hval_s : ∑ w ∈ hfin.toFinset, (fun z => if z = x then (1 : ℝ) else 0) w = 1 := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hbx
      simp [hbx]
    · intro hxnot
      exact absurd hxmem hxnot
  refine ⟨fun z => if z = x then 1 else 0, hfin, ?_, ?_, ?_⟩
  · exact hval_v.symm
  · intro z hz
    have hzx : z ≠ x := fun h => hx (h ▸ hz)
    simp [hzx]
  · exact hval_s

/-- 两不同单点集的交为空。 -/
theorem p11w2_single_inter_single {v w : V3} (hvw : v ≠ w) :
    ({v} : Set V3) ∩ {w} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [Set.mem_singleton_iff] at hz1 hz2
  exact hvw (hz1.symm.trans hz2)

/-- 单点与两点集的交为空。 -/
theorem p11w2_single_inter_pair {z u v : V3} (hzu : z ≠ u) (hzv : z ≠ v) :
    ({z} : Set V3) ∩ {u, v} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  rw [Set.mem_singleton_iff] at ht1
  subst ht1
  rcases Set.mem_insert_iff.mp ht2 with h | h
  · exact hzu h
  · rw [Set.mem_singleton_iff] at h
    exact hzv h

/-- `affGt ⊆ affGe`（同见证，`0 < r ⟹ 0 ≤ r`）。 -/
theorem P11W2_GT_SUB_GE {s t : Set V3} : affGt s t ⊆ affGe s t := by
  intro y hy
  obtain ⟨f, hfin, hv, hpos, hone⟩ := hy
  exact ⟨f, hfin, hv, fun z hz => le_of_lt (hpos z hz), hone⟩

/-- 项杀手（FAN7）：`t ∈ affGt {x} e`、`t ∈ affGe {x} {z}`，`z` 与边 `e`
在 `hve` 下两锥不交 ⟹ 只有退化可能 `t = x`。 -/
theorem p11w2_gt_inter_ge_single {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    {z : V3} (hzV : z ∈ V) {e : Set V3} (he : e ∈ E)
    (hxz : x ≠ z) {t : V3} (hgt : t ∈ affGt {x} e) (hge : t ∈ affGe {x} {z}) :
    t = x := by
  obtain ⟨a, ha, hta⟩ := (P11W2_GE_SINGLE_REL hxz).mp hge
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← sub_eq_zero]
    rw [← ha0] at hta
    simpa using hta
  · exfalso
    have hmem : t ∈ affGt {x} {z} ∩ affGt {x} e :=
      ⟨P11W2_GT_SINGLE_REL hxz hapos hta, hgt⟩
    rw [hve z hzV e he] at hmem
    simpa using hmem

end W11b2p2Kit

/-- 空交情形（边 × 边）：两条不同的图边，`affGe` 之交只有基点。 -/
private theorem p11w2_empty_two_edges {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hg : Graph E) (hsubV : ∀ e ∈ E, e ⊆ V) (hsubx : ∀ e ∈ E, x ∉ e)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅)
    {e1 e2 : Set V3} (he1E : e1 ∈ E) (he2E : e2 ∈ E) (hemp : e1 ∩ e2 = ∅) :
    affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3) := by
  obtain ⟨u, v, huv, rfl⟩ := P11W2_EDGE_PAIR hg he1E
  obtain ⟨y, z, hyz, rfl⟩ := P11W2_EDGE_PAIR hg he2E
  have huV : u ∈ V := hsubV {u, v} he1E (by simp)
  have hvV : v ∈ V := hsubV {u, v} he1E (by simp)
  have hyV : y ∈ V := hsubV {y, z} he2E (by simp)
  have hzV : z ∈ V := hsubV {y, z} he2E (by simp)
  have hxu : x ≠ u := fun h => hsubx {u, v} he1E (by rw [← h]; simp)
  have hxv : x ≠ v :=
    fun h => hsubx {u, v} he1E (by rw [← h]; simp)
  have hxy : x ≠ y := fun h => hsubx {y, z} he2E (by rw [← h]; simp)
  have hxz : x ≠ z :=
    fun h => hsubx {y, z} he2E (by rw [← h]; simp)
  have hempty : ∀ t : V3, t ∈ ({u, v} : Set V3) → t ∈ ({y, z} : Set V3) → False := by
    intro t h1 h2
    have hmem : t ∈ ({u, v} : Set V3) ∩ {y, z} := ⟨h1, h2⟩
    rw [hemp] at hmem
    exact hmem
  have huy : u ≠ y := fun h => hempty y (by rw [← h]; simp) (by simp)
  have huz : u ≠ z :=
    fun h => hempty z (by rw [← h]; simp)
      (by simp)
  have hvy : v ≠ y :=
    fun h => hempty y (by rw [← h]; simp)
      (by simp)
  have hvz : v ≠ z :=
    fun h => hempty z (by rw [← h]; simp)
      (by simp)
  have hne : ({u, v} : Set V3) ≠ {y, z} := by
    intro h
    have hmem : u ∈ ({y, z} : Set V3) := by rw [← h]; simp
    rcases Set.mem_insert_iff.mp hmem with h' | h'
    · exact huy h'
    · rw [Set.mem_singleton_iff] at h'
      exact huz h'
  have hfin1 : ({x} ∪ {u, v} : Set V3).Finite :=
    (Set.finite_singleton x).union (hg {u, v} he1E).1
  have hfin2 : ({x} ∪ {y, z} : Set V3).Finite :=
    (Set.finite_singleton x).union (hg {y, z} he2E).1
  rw [AFF_GE_TO_AFF_GT2_GE1 (x := x) (u := u) (v := v) (Ne.symm hxu) (Ne.symm hxv),
    AFF_GE_TO_AFF_GT2_GE1 (x := x) (u := y) (v := z) (Ne.symm hxy) (Ne.symm hxz)]
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Set.mem_union] at ht1 ht2
    rcases ht1 with (h1a | h1b) | h1c <;> rcases ht2 with (h2a | h2b) | h2c
    · have hmem : t ∈ affGt {x} {u, v} ∩ affGt {x} {y, z} := ⟨h1a, h2a⟩
      rw [hee {u, v} he1E {y, z} he2E hne] at hmem
      exact absurd hmem (by simp)
    · have ht' : t = x := p11w2_gt_inter_ge_single hve hyV he1E hxy h1a h2b
      rw [Set.mem_singleton_iff, ht']
    · have ht' : t = x := p11w2_gt_inter_ge_single hve hzV he1E hxz h1a h2c
      rw [Set.mem_singleton_iff, ht']
    · have ht' : t = x := p11w2_gt_inter_ge_single hve huV he2E hxu h2a h1b
      rw [Set.mem_singleton_iff, ht']
    · have hmem : t ∈ affGe {x} {u} ∩ affGe {x} {y} := ⟨h1b, h2b⟩
      rw [hvs u huV y hyV, p11w2_single_inter_single huy, P11W_AFFGE_EMPTY] at hmem
      exact hmem
    · have hmem : t ∈ affGe {x} {u} ∩ affGe {x} {z} := ⟨h1b, h2c⟩
      rw [hvs u huV z hzV, p11w2_single_inter_single huz, P11W_AFFGE_EMPTY] at hmem
      exact hmem
    · have ht' : t = x := p11w2_gt_inter_ge_single hve hvV he2E hxv h2a h1c
      rw [Set.mem_singleton_iff, ht']
    · have hmem : t ∈ affGe {x} {v} ∩ affGe {x} {y} := ⟨h1c, h2b⟩
      rw [hvs v hvV y hyV, p11w2_single_inter_single hvy, P11W_AFFGE_EMPTY] at hmem
      exact hmem
    · have hmem : t ∈ affGe {x} {v} ∩ affGe {x} {z} := ⟨h1c, h2c⟩
      rw [hvs v hvV z hzV, p11w2_single_inter_single hvz, P11W_AFFGE_EMPTY] at hmem
      exact hmem
  · intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact ⟨Or.inr (p11w2_mem_self_affGe
        ((Set.finite_singleton x).union (Set.finite_singleton v)) (by simp [hxv])),
      Or.inr (p11w2_mem_self_affGe
        ((Set.finite_singleton x).union (Set.finite_singleton z)) (by simp [hxz]))⟩

/-- 空交情形（边 × 单点）：单点不在边上时 `affGe` 之交只有基点。 -/
private theorem p11w2_empty_edge_single {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hg : Graph E) (hxV : x ∉ V) (hsubV : ∀ e ∈ E, e ⊆ V)
    (hsubx : ∀ e ∈ E, x ∉ e)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    {e : Set V3} (heE : e ∈ E) {b : V3} (hbV : b ∈ V) (hb1 : b ∉ e) :
    affGe {x} e ∩ affGe {x} {b} = ({x} : Set V3) := by
  obtain ⟨u, w, huw, rfl⟩ := P11W2_EDGE_PAIR hg heE
  have huV : u ∈ V := hsubV {u, w} heE (by simp)
  have hwV : w ∈ V := hsubV {u, w} heE (by simp)
  have hxu : x ≠ u := fun h => hsubx {u, w} heE (by rw [← h]; simp)
  have hxw : x ≠ w :=
    fun h => hsubx {u, w} heE (by rw [← h]; simp)
  have hxb : x ≠ b := fun h => hxV (h ▸ hbV)
  have hbu : b ≠ u := fun h => hb1 (by rw [h]; simp)
  have hbw : b ≠ w := fun h => hb1 (by rw [h]; simp)
  have hfin1 : ({x} ∪ {b} : Set V3).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton b)
  have hfin2 : ({x} ∪ {u, w} : Set V3).Finite :=
    (Set.finite_singleton x).union (hg {u, w} heE).1
  rw [AFF_GE_TO_AFF_GT2_GE1 (x := x) (u := u) (v := w) (Ne.symm hxu) (Ne.symm hxw)]
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Set.mem_union] at ht1
    rcases ht1 with (h1a | h1b) | h1c
    · have ht' : t = x := p11w2_gt_inter_ge_single hve hbV heE hxb h1a ht2
      rw [Set.mem_singleton_iff, ht']
    · have hmem : t ∈ affGe {x} {b} ∩ affGe {x} {u} := ⟨ht2, h1b⟩
      rw [hvs b hbV u huV, p11w2_single_inter_single hbu, P11W_AFFGE_EMPTY] at hmem
      exact hmem
    · have hmem : t ∈ affGe {x} {b} ∩ affGe {x} {w} := ⟨ht2, h1c⟩
      rw [hvs b hbV w hwV, p11w2_single_inter_single hbw, P11W_AFFGE_EMPTY] at hmem
      exact hmem
  · intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact ⟨Or.inr (p11w2_mem_self_affGe
        ((Set.finite_singleton x).union (Set.finite_singleton w)) (by simp [hxw])),
      p11w2_mem_self_affGe hfin1 (by simp [hxb])⟩

/-- 空交情形（单点 × 单点）：两不同顶点的 `affGe` 之交只有基点。 -/
private theorem p11w2_empty_two_singles {x : V3} {V : Set V3}
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    {a b : V3} (haV : a ∈ V) (hbV : b ∈ V) (hab : a ≠ b) :
    affGe {x} {a} ∩ affGe {x} {b} = ({x} : Set V3) := by
  rw [hvs a haV b hbV, p11w2_single_inter_single hab, P11W_AFFGE_EMPTY]

/-- `fan7` 的空交条件（`hvs`/`hve` 版本）。 -/
private theorem p11w2_fan7_empty (x : V3) (V : Set V3) (E : Set (Set V3))
    (hg : Graph E) (hxV : x ∉ V)
    (hsubV : ∀ e ∈ E, e ⊆ V) (hsubx : ∀ e ∈ E, x ∉ e)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅)
    {e1 e2 : Set V3} (he1 : e1 ∈ E ∪ (image (fun v : V3 => {v}) V))
    (he2 : e2 ∈ E ∪ (image (fun v : V3 => {v}) V))
    (hemp : e1 ∩ e2 = ∅) :
    affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3) := by
  have hu1 : e1 ∈ E ∨ e1 ∈ image (fun v : V3 => {v}) V := by
    simpa only [Set.mem_union] using he1
  have hu2 : e2 ∈ E ∨ e2 ∈ image (fun v : V3 => {v}) V := by
    simpa only [Set.mem_union] using he2
  rcases hu1 with he1E | ⟨a, haV, rfl⟩
  · rcases hu2 with he2E | ⟨b, hbV, rfl⟩
    · exact p11w2_empty_two_edges hg hsubV hsubx hvs hve hee he1E he2E hemp
    · have hb1 : b ∉ e1 := by
        intro hb
        have hmem : b ∈ e1 ∩ ({b} : Set V3) := ⟨hb, Set.mem_singleton b⟩
        rw [hemp] at hmem
        exact hmem
      exact p11w2_empty_edge_single hg hxV hsubV hsubx hvs hve he1E hbV hb1
  · rcases hu2 with he2E | ⟨b, hbV, rfl⟩
    · have ha1 : a ∉ e2 := by
        intro ha
        have hmem : a ∈ ({a} : Set V3) ∩ e2 := ⟨Set.mem_singleton a, ha⟩
        rw [hemp] at hmem
        exact hmem
      rw [Set.inter_comm (affGe {x} {a}) (affGe {x} e2)]
      exact p11w2_empty_edge_single hg hxV hsubV hsubx hvs hve he2E haV ha1
    · have hab : a ≠ b := by
        intro h
        have hmem : a ∈ ({a} : Set V3) ∩ {b} :=
          ⟨Set.mem_singleton a, by rw [h]; exact Set.mem_singleton b⟩
        rw [hemp] at hmem
        exact hmem
      exact p11w2_empty_two_singles hvs haV hbV hab

/-- HOL `FAN7_AFF_GT_CONDITION` (polar_fan.hl:661). -/
theorem FAN7_AFF_GT_CONDITION (x : V3) (V : Set V3) (E : Set (Set V3))
    (hg : Graph E) (hx : x ∉ V)
    (hsub : ∀ e ∈ E, e ⊆ V ∧ x ∉ e)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅) :
    fan7 x V E := by
  intro e1 he1 e2 he2
  by_cases heq : e1 = e2
  · rw [heq, Set.inter_self, Set.inter_self]
  · rcases p11w_edge_trichotomy (V := V) hg
      (by rw [p11w_img_singleton_eq]; exact he1)
      (by rw [p11w_img_singleton_eq]; exact he2) with heq' | hemp | ⟨v, hv⟩
    · exact absurd heq' heq
    · rw [hemp, P11W_AFFGE_EMPTY]
      exact p11w2_fan7_empty x V E hg hx (fun e he => (hsub e he).1)
        (fun e he => (hsub e he).2) hvs hve hee
        (by rw [p11w_img_singleton_eq]; exact he1)
        (by rw [p11w_img_singleton_eq]; exact he2) hemp
    · rw [hv]
      have hv1 : v ∈ e1 := by
        have h : v ∈ e1 ∩ e2 := by rw [hv]; exact Set.mem_singleton v
        exact h.1
      have hv2 : v ∈ e2 := by
        have h : v ∈ e1 ∩ e2 := by rw [hv]; exact Set.mem_singleton v
        exact h.2
      have hfinv : ({x} ∪ {v} : Set V3).Finite :=
        (Set.finite_singleton x).union (Set.finite_singleton v)
      have hu1 : e1 ∈ E ∨ e1 ∈ image (fun v : V3 => {v}) V := by
        rw [p11w_img_singleton_eq]
        simpa only [Set.mem_union] using he1
      have hu2 : e2 ∈ E ∨ e2 ∈ image (fun v : V3 => {v}) V := by
        rw [p11w_img_singleton_eq]
        simpa only [Set.mem_union] using he2
      rcases hu1 with he1E | ⟨a, haV, rfl⟩
      · rcases hu2 with he2E | ⟨b, hbV, rfl⟩
        · -- 边 × 边，共享 v
          obtain ⟨u, huv, he1eq⟩ := P11W2_EDGE_PAIR_OF_MEM hg he1E hv1
          obtain ⟨z, hzv, he2eq⟩ := P11W2_EDGE_PAIR_OF_MEM hg he2E hv2
          rw [he1eq, he2eq, Set.pair_comm z v]
          have he1E' : ({u, v} : Set V3) ∈ E := by rw [← he1eq]; exact he1E
          have he2E' : ({v, z} : Set V3) ∈ E := by
            rw [Set.pair_comm v z, ← he2eq]; exact he2E
          have huV : u ∈ V := (hsub {u, v} he1E').1 (by simp)
          have hvV : v ∈ V :=
            (hsub {u, v} he1E').1 (by simp)
          have hzV : z ∈ V :=
            (hsub {v, z} he2E').1 (by simp)
          have hxu : x ≠ u := fun h => (hsub {u, v} he1E').2 (by rw [← h]; simp)
          have hxv : x ≠ v :=
            fun h => (hsub {u, v} he1E').2 (by rw [← h]; simp)
          have hxz : x ≠ z :=
            fun h => (hsub {v, z} he2E').2 (by rw [← h]; simp)
          have huz : u ≠ z := by
            intro h
            apply heq
            rw [he1eq, he2eq, h]
          have hfin1 : ({u, v} : Set V3).Finite := (hg {u, v} he1E').1
          have hfin2 : ({v, z} : Set V3).Finite := (hg {v, z} he2E').1
          rw [AFF_GE_TO_AFF_GT2_GE1 (x := x) (u := u) (v := v) (Ne.symm hxu) (Ne.symm hxv),
            AFF_GE_TO_AFF_GT2_GE1 (x := x) (u := v) (v := z) (Ne.symm hxv) (Ne.symm hxz)]
          apply Set.Subset.antisymm
          · intro t ht
            obtain ⟨ht1, ht2⟩ := ht
            simp only [Set.mem_union] at ht1 ht2
            rcases ht1 with (h1a | h1b) | h1c <;> rcases ht2 with (h2a | h2b) | h2c
            · have hmem : t ∈ affGt {x} {u, v} ∩ affGt {x} {v, z} := ⟨h1a, h2a⟩
              have hne : ({u, v} : Set V3) ≠ {v, z} := by
                intro h
                have hmem' : u ∈ ({v, z} : Set V3) := by rw [← h]; simp
                rcases Set.mem_insert_iff.mp hmem' with h' | h'
                · exact huv h'
                · rw [Set.mem_singleton_iff] at h'
                  exact huz h'
              rw [hee {u, v} he1E' {v, z} he2E' hne] at hmem
              exact absurd hmem (by simp)
            · exact h2b
            · have ht' : t = x := p11w2_gt_inter_ge_single hve hzV he1E' hxz h1a h2c
              rw [ht']
              exact p11w2_mem_self_affGe hfinv (by simp [hxv])
            · have ht' : t = x := p11w2_gt_inter_ge_single hve huV he2E' hxu h2a h1b
              rw [ht']
              exact p11w2_mem_self_affGe hfinv (by simp [hxv])
            · have hmem : t ∈ affGe {x} {u} ∩ affGe {x} {v} := ⟨h1b, h2b⟩
              rw [hvs u huV v hvV, p11w2_single_inter_single huv, P11W_AFFGE_EMPTY] at hmem
              rw [Set.mem_singleton_iff] at hmem
              rw [hmem]
              exact p11w2_mem_self_affGe hfinv (by simp [hxv])
            · have hmem : t ∈ affGe {x} {u} ∩ affGe {x} {z} := ⟨h1b, h2c⟩
              rw [hvs u huV z hzV, p11w2_single_inter_single huz, P11W_AFFGE_EMPTY] at hmem
              rw [Set.mem_singleton_iff] at hmem
              rw [hmem]
              exact p11w2_mem_self_affGe hfinv (by simp [hxv])
            · exact h1c
            · exact h1c
            · have hmem : t ∈ affGe {x} {v} ∩ affGe {x} {z} := ⟨h1c, h2c⟩
              rw [hvs v hvV z hzV, p11w2_single_inter_single hzv.symm, P11W_AFFGE_EMPTY] at hmem
              rw [Set.mem_singleton_iff] at hmem
              rw [hmem]
              exact p11w2_mem_self_affGe hfinv (by simp [hxv])
          · intro t ht
            exact ⟨Or.inr ht, Or.inl (Or.inr ht)⟩
        · -- e1 边，e2 = {b} 单点
          have hvb : v = b := by
            have hmem : v ∈ e1 ∩ ({b} : Set V3) := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.2
          rw [hvb]
          have hinter : e1 ∩ ({b} : Set V3) = ({b} : Set V3) := by
            rw [hv, ← hvb]
          have hb1 : b ∈ e1 := by
            have hmem : b ∈ e1 ∩ ({b} : Set V3) := by
              rw [hinter]; exact Set.mem_singleton b
            exact hmem.1
          apply Set.Subset.antisymm
          · exact Set.inter_subset_right
          · intro t ht
            exact ⟨P11W_AFFGE_MONO_SINGLE (t := ({b} : Set V3)) (t' := e1)
              (by
                intro y hy
                rw [Set.mem_singleton_iff] at hy
                rw [hy]
                exact hb1) (hsub e1 he1E).2 (hg e1 he1E).1 ht, ht⟩
      · rcases hu2 with he2E | ⟨b, hbV, rfl⟩
        · -- e1 = {a} 单点，e2 边
          have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ e2 := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.1
          rw [hva]
          have hinter : ({a} : Set V3) ∩ e2 = ({a} : Set V3) := by
            rw [hv, ← hva]
          have ha2 : a ∈ e2 := by
            have hmem : a ∈ ({a} : Set V3) ∩ e2 := by
              rw [hinter]; exact Set.mem_singleton a
            exact hmem.2
          apply Set.Subset.antisymm
          · exact Set.inter_subset_left
          · intro t ht
            exact ⟨ht, P11W_AFFGE_MONO_SINGLE (t := ({a} : Set V3)) (t' := e2)
              (by
                intro y hy
                rw [Set.mem_singleton_iff] at hy
                rw [hy]
                exact ha2) (hsub e2 he2E).2 (hg e2 he2E).1 ht⟩
        · -- 两个单点
          have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ {b} := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.1
          have hvb : v = b := by
            have hmem : v ∈ ({a} : Set V3) ∩ {b} := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.2
          rw [← hva, ← hvb, Set.inter_self]


/-- HOL `FAN_AFF_GT_CONDITION` (polar_fan.hl:812). -/
theorem FAN_AFF_GT_CONDITION (x : V3) (V : Set V3) (E : Set (Set V3))
    (hun : (⋃₀ E) ⊆ V) (hg : Graph E) (hf1 : fan1 x V E) (hf2 : fan2 x V E)
    (hf6 : fan6 x V E)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅) :
    FAN x V E := by
  refine ⟨hun, hg, hf1, hf2, hf6, ?_⟩
  exact FAN7_AFF_GT_CONDITION x V E hg hf2
    (fun e he => ⟨fun z hz => hun (Set.subset_sUnion_of_mem he hz),
      fun h => hf2 (hun (Set.subset_sUnion_of_mem he h))⟩)
    hvs hve hee

/-- `affGt {x} {u,v}` 的差向量系数形（严格正；`Affsign` 消去）。 -/
private theorem p11w2_gt_pair_rel_elim {x u v y : V3}
    (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    (h : y ∈ affGt {x} {u, v}) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ y - x = a • (u - x) + b • (v - x) := by
  obtain ⟨f, hfin, hvec, hsign, hone⟩ := h
  have h3 : hfin.toFinset = ({x, u, v} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h3, Finset.sum_insert (by simp [hxu, hxv]),
    Finset.sum_insert (Finset.notMem_singleton.mpr huv),
    Finset.sum_singleton] at hvec hone
  refine ⟨f u, f v, hsign u (by simp), hsign v (by simp), ?_⟩
  have hfx : f x = 1 - f u - f v := by linarith
  rw [hvec, hfx]
  module

/-- 共享点两边的 `affGt` 之交为空（空交充分条件 `h0` 的推论）：系数
`b` 与 `c` 比较，`u` 或 `z` 被推入另一侧的闭锥，与 `h0` 冲突。 -/
private theorem p11w2_gt_inter_gt_shared_empty {x : V3} {V : Set V3} {E : Set (Set V3)}
    (h0 : ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
      ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
        e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3))
    {u v z : V3} (huV : u ∈ V) (hzV : z ∈ V)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxz : x ≠ z)
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (he1 : ({u, v} : Set V3) ∈ E) (he2 : ({v, z} : Set V3) ∈ E)
    {t : V3} (h1 : t ∈ affGt {x} {u, v}) (h2 : t ∈ affGt {x} {v, z}) : False := by
  obtain ⟨a, b, ha, hb, hta⟩ := p11w2_gt_pair_rel_elim hxu hxv huv h1
  obtain ⟨c, d, hc, hd, htb⟩ := p11w2_gt_pair_rel_elim hxv hxz hvz h2
  have hkey : a • (u - x) = (c - b) • (v - x) + d • (z - x) := by
    have h := hta.symm.trans htb
    calc a • (u - x) = (a • (u - x) + b • (v - x)) - b • (v - x) := by abel
      _ = (c • (v - x) + d • (z - x)) - b • (v - x) := by rw [h]
      _ = (c - b) • (v - x) + d • (z - x) := by module
  rcases le_total b c with hbc | hcb
  · -- b ≤ c：u ∈ 闭锥 {v,z}，与 h0 ({u} ∩ {v,z} = ∅) 冲突
    have hmem : u ∈ affGe {x} {v, z} :=
      (P11W2_GE_PAIR_REL hxv hxz hvz).mpr
        ⟨a⁻¹ * (c - b), a⁻¹ * d,
          mul_nonneg (le_of_lt (inv_pos.mpr ha)) (by linarith),
          mul_nonneg (le_of_lt (inv_pos.mpr ha)) (le_of_lt hd), by
            have h := congrArg (fun y => a⁻¹ • y) hkey
            rw [smul_add, smul_smul, smul_smul, smul_smul,
              inv_mul_cancel₀ ha.ne', one_smul] at h
            exact h⟩
    have hemp : ({u} : Set V3) ∩ {v, z} = ∅ := p11w2_single_inter_pair huv huz
    have humem : u ∈ affGe {x} {u} :=
      (P11W2_GE_SINGLE_REL hxu).mpr ⟨1, zero_le_one, by rw [one_smul]⟩
    have hmem' : u ∈ affGe {x} {u} ∩ affGe {x} {v, z} := ⟨humem, hmem⟩
    have h := h0 {u} (Set.mem_union_right _ ⟨u, huV, rfl⟩) {v, z}
      (Set.mem_union_left _ he2) hemp
    rw [h] at hmem'
    rw [Set.mem_singleton_iff] at hmem'
    exact hxu hmem'.symm
  · -- c ≤ b：z ∈ 闭锥 {u,v}，与 h0 ({z} ∩ {u,v} = ∅) 冲突
    have hmem : z ∈ affGe {x} {u, v} :=
      (P11W2_GE_PAIR_REL hxu hxv huv).mpr
        ⟨d⁻¹ * a, d⁻¹ * (b - c),
          mul_nonneg (le_of_lt (inv_pos.mpr hd)) (le_of_lt ha),
          mul_nonneg (le_of_lt (inv_pos.mpr hd)) (by linarith), by
            have h := congrArg (fun y => d⁻¹ • y) hkey
            rw [smul_add, smul_smul, smul_smul, smul_smul,
              inv_mul_cancel₀ hd.ne', one_smul] at h
            have h' : z - x = (d⁻¹ * a) • (u - x) - (d⁻¹ * (c - b)) • (v - x) := by
              rw [eq_sub_iff_add_eq, add_comm]
              exact h.symm
            have hcoef : (d⁻¹ * (b - c)) • (v - x) = -((d⁻¹ * (c - b)) • (v - x)) := by
              rw [← neg_smul]
              congr 1
              ring
            rw [hcoef, ← sub_eq_add_neg]
            exact h'⟩
    have hemp : ({z} : Set V3) ∩ {u, v} = ∅ := p11w2_single_inter_pair huz.symm hvz.symm
    have hzmem : z ∈ affGe {x} {z} :=
      (P11W2_GE_SINGLE_REL hxz).mpr ⟨1, zero_le_one, by rw [one_smul]⟩
    have hmem' : z ∈ affGe {x} {z} ∩ affGe {x} {u, v} := ⟨hzmem, hmem⟩
    have h := h0 {z} (Set.mem_union_right _ ⟨z, hzV, rfl⟩) {u, v}
      (Set.mem_union_left _ he1) hemp
    rw [h] at hmem'
    rw [Set.mem_singleton_iff] at hmem'
    exact hxz hmem'.symm

/-- 共享点两边的闭锥：`affGe {x} {u,v} ∩ affGe {x} {v,z} = affGe {x} {v}`
（`GMLWKPK_SIMPLE` 的单交情形核心；`h0` 为全部空交对的条件）。 -/
private theorem p11w2_shared_two_edges {x : V3} {V : Set V3} {E : Set (Set V3)}
    (h0 : ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
      ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
        e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3))
    {u v z : V3} (huV : u ∈ V) (hvV : v ∈ V) (hzV : z ∈ V)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxz : x ≠ z)
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (he1 : ({u, v} : Set V3) ∈ E) (he2 : ({v, z} : Set V3) ∈ E) :
    affGe {x} {u, v} ∩ affGe {x} {v, z} = affGe {x} {v} := by
  have hfinv : ({x} ∪ {v} : Set V3).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton v)
  rw [AFF_GE_TO_AFF_GT2_GE1 (x := x) (u := u) (v := v) (Ne.symm hxu) (Ne.symm hxv),
    AFF_GE_TO_AFF_GT2_GE1 (x := x) (u := v) (v := z) (Ne.symm hxv) (Ne.symm hxz)]
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Set.mem_union] at ht1 ht2
    rcases ht1 with (h1a | h1b) | h1c <;> rcases ht2 with (h2a | h2b) | h2c
    · exact (p11w2_gt_inter_gt_shared_empty h0 huV hzV hxu hxv hxz huv huz hvz
        he1 he2 h1a h2a).elim
    · exact h2b
    · -- Gt{u,v} ∩ Ge{z}
      obtain ⟨e, he0, hte⟩ := (P11W2_GE_SINGLE_REL hxz).mp h2c
      rcases eq_or_lt_of_le he0 with he0' | hepos
      · have ht' : t = x := by
          rw [← sub_eq_zero, hte, ← he0', zero_smul]
        rw [ht']
        exact p11w2_mem_self_affGe hfinv (by simp [hxv])
      · have hgt : t ∈ affGt {x} {z} := P11W2_GT_SINGLE_REL hxz hepos hte
        have hmem : t ∈ affGe {x} {z} ∩ affGe {x} {u, v} :=
          ⟨P11W2_GT_SUB_GE hgt, P11W2_GT_SUB_GE h1a⟩
        have hemp : ({z} : Set V3) ∩ {u, v} = ∅ := p11w2_single_inter_pair huz.symm hvz.symm
        have h := h0 {z} (Set.mem_union_right _ ⟨z, hzV, rfl⟩) {u, v}
          (Set.mem_union_left _ he1) hemp
        rw [h] at hmem
        rw [Set.mem_singleton_iff] at hmem
        rw [hmem]
        exact p11w2_mem_self_affGe hfinv (by simp [hxv])
    · -- Ge{u} ∩ Gt{v,z}
      obtain ⟨e, he0, hte⟩ := (P11W2_GE_SINGLE_REL hxu).mp h1b
      rcases eq_or_lt_of_le he0 with he0' | hepos
      · have ht' : t = x := by
          rw [← sub_eq_zero, hte, ← he0', zero_smul]
        rw [ht']
        exact p11w2_mem_self_affGe hfinv (by simp [hxv])
      · have hgt : t ∈ affGt {x} {u} := P11W2_GT_SINGLE_REL hxu hepos hte
        have hmem : t ∈ affGe {x} {u} ∩ affGe {x} {v, z} :=
          ⟨P11W2_GT_SUB_GE hgt, P11W2_GT_SUB_GE h2a⟩
        have hemp : ({u} : Set V3) ∩ {v, z} = ∅ := p11w2_single_inter_pair huv huz
        have h := h0 {u} (Set.mem_union_right _ ⟨u, huV, rfl⟩) {v, z}
          (Set.mem_union_left _ he2) hemp
        rw [h] at hmem
        rw [Set.mem_singleton_iff] at hmem
        rw [hmem]
        exact p11w2_mem_self_affGe hfinv (by simp [hxv])
    · -- Ge{u} ∩ Ge{v}
      have hmem : t ∈ affGe {x} {u} ∩ affGe {x} {v} := ⟨h1b, h2b⟩
      have hemp : ({u} : Set V3) ∩ {v} = ∅ := p11w2_single_inter_single huv
      have h := h0 {u} (Set.mem_union_right _ ⟨u, huV, rfl⟩) {v}
        (Set.mem_union_right _ ⟨v, hvV, rfl⟩) hemp
      rw [h, Set.mem_singleton_iff] at hmem
      rw [hmem]
      exact p11w2_mem_self_affGe hfinv (by simp [hxv])
    · -- Ge{u} ∩ Ge{z}
      have hmem : t ∈ affGe {x} {u} ∩ affGe {x} {z} := ⟨h1b, h2c⟩
      have hemp : ({u} : Set V3) ∩ {z} = ∅ := p11w2_single_inter_single huz
      have h := h0 {u} (Set.mem_union_right _ ⟨u, huV, rfl⟩) {z}
        (Set.mem_union_right _ ⟨z, hzV, rfl⟩) hemp
      rw [h, Set.mem_singleton_iff] at hmem
      rw [hmem]
      exact p11w2_mem_self_affGe hfinv (by simp [hxv])
    · exact h1c
    · exact h1c
    · -- Ge{v} ∩ Ge{z}
      have hmem : t ∈ affGe {x} {v} ∩ affGe {x} {z} := ⟨h1c, h2c⟩
      have hemp : ({v} : Set V3) ∩ {z} = ∅ := p11w2_single_inter_single hvz
      have h := h0 {v} (Set.mem_union_right _ ⟨v, hvV, rfl⟩) {z}
        (Set.mem_union_right _ ⟨z, hzV, rfl⟩) hemp
      rw [h, Set.mem_singleton_iff] at hmem
      rw [hmem]
      exact p11w2_mem_self_affGe hfinv (by simp [hxv])
  · intro t ht
    exact ⟨Or.inr ht, Or.inl (Or.inr ht)⟩

/-- `fan7` 的空交充分条件（GMLWKPK_SIMPLE 的核心）：全部空交对的
`affGe` 之交退化为基点 ⟹ `fan7`。 -/
private theorem p11w2_fan7_of_empty_cond (x : V3) (V : Set V3) (E : Set (Set V3))
    (hg : Graph E) (hsubV : ∀ e ∈ E, e ⊆ V) (hsubx : ∀ e ∈ E, x ∉ e)
    (h0 : ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
      ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
        e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) :
    fan7 x V E := by
  intro e1 he1 e2 he2
  have he1i : e1 ∈ E ∪ (image (fun v : V3 => {v}) V) := by
    rw [p11w_img_singleton_eq]; exact he1
  have he2i : e2 ∈ E ∪ (image (fun v : V3 => {v}) V) := by
    rw [p11w_img_singleton_eq]; exact he2
  by_cases heq : e1 = e2
  · rw [heq, Set.inter_self, Set.inter_self]
  · rcases p11w_edge_trichotomy (V := V) hg he1i he2i with heq' | hemp | ⟨v, hv⟩
    · exact absurd heq' heq
    · rw [hemp, P11W_AFFGE_EMPTY]
      exact h0 e1 he1i e2 he2i hemp
    · rw [hv]
      have hv1 : v ∈ e1 := by
        have h : v ∈ e1 ∩ e2 := by rw [hv]; exact Set.mem_singleton v
        exact h.1
      have hv2 : v ∈ e2 := by
        have h : v ∈ e1 ∩ e2 := by rw [hv]; exact Set.mem_singleton v
        exact h.2
      have hfinv : ({x} ∪ {v} : Set V3).Finite :=
        (Set.finite_singleton x).union (Set.finite_singleton v)
      rcases he1i with he1E | ⟨a, haV, rfl⟩
      · rcases he2i with he2E | ⟨b, hbV, rfl⟩
        · -- 边 × 边，共享 v
          obtain ⟨u, huv, he1eq⟩ := P11W2_EDGE_PAIR_OF_MEM hg he1E hv1
          obtain ⟨z, hzv, he2eq⟩ := P11W2_EDGE_PAIR_OF_MEM hg he2E hv2
          rw [he1eq, he2eq, Set.pair_comm z v]
          have he1E' : ({u, v} : Set V3) ∈ E := by rw [← he1eq]; exact he1E
          have he2E' : ({v, z} : Set V3) ∈ E := by
            rw [Set.pair_comm v z, ← he2eq]; exact he2E
          have huV : u ∈ V := hsubV {u, v} he1E' (by simp)
          have hvV : v ∈ V := hsubV {u, v} he1E' (by simp)
          have hzV : z ∈ V := hsubV {v, z} he2E' (by simp)
          have hxu : x ≠ u := fun h => hsubx {u, v} he1E' (by rw [← h]; simp)
          have hxv : x ≠ v := fun h => hsubx {u, v} he1E' (by rw [← h]; simp)
          have hxz : x ≠ z := fun h => hsubx {v, z} he2E' (by rw [← h]; simp)
          have huz : u ≠ z := by
            intro h
            apply heq
            rw [he1eq, he2eq, h]
          exact p11w2_shared_two_edges h0 huV hvV hzV hxu hxv hxz huv huz
            hzv.symm he1E' he2E'
        · -- e1 边，e2 = {b} 单点
          have hvb : v = b := by
            have hmem : v ∈ e1 ∩ ({b} : Set V3) := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.2
          rw [hvb]
          have hinter : e1 ∩ ({b} : Set V3) = ({b} : Set V3) := by
            rw [hv, ← hvb]
          have hb1 : b ∈ e1 := by
            have hmem : b ∈ e1 ∩ ({b} : Set V3) := by
              rw [hinter]; exact Set.mem_singleton b
            exact hmem.1
          apply Set.Subset.antisymm
          · exact Set.inter_subset_right
          · intro t ht
            exact ⟨P11W_AFFGE_MONO_SINGLE (t := ({b} : Set V3)) (t' := e1)
              (by
                intro y hy
                rw [Set.mem_singleton_iff] at hy
                rw [hy]
                exact hb1) (hsubx e1 he1E) (hg e1 he1E).1 ht, ht⟩
      · rcases he2i with he2E | ⟨b, hbV, rfl⟩
        · -- e1 = {a} 单点，e2 边
          have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ e2 := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.1
          rw [hva]
          have hinter : ({a} : Set V3) ∩ e2 = ({a} : Set V3) := by
            rw [hv, ← hva]
          have ha2 : a ∈ e2 := by
            have hmem : a ∈ ({a} : Set V3) ∩ e2 := by
              rw [hinter]; exact Set.mem_singleton a
            exact hmem.2
          apply Set.Subset.antisymm
          · exact Set.inter_subset_left
          · intro t ht
            exact ⟨ht, P11W_AFFGE_MONO_SINGLE (t := ({a} : Set V3)) (t' := e2)
              (by
                intro y hy
                rw [Set.mem_singleton_iff] at hy
                rw [hy]
                exact ha2) (hsubx e2 he2E) (hg e2 he2E).1 ht⟩
        · -- 两个单点
          have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ {b} := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.1
          have hvb : v = b := by
            have hmem : v ∈ ({a} : Set V3) ∩ {b} := by rw [hv]; exact Set.mem_singleton v
            exact Set.mem_singleton_iff.mp hmem.2
          rw [← hva, ← hvb, Set.inter_self]

/-- HOL `GMLWKPK_SIMPLE` (polar_fan.hl:832). -/
theorem GMLWKPK_SIMPLE (x : V3) (V : Set V3) (E : Set (Set V3))
    (hun : (⋃₀ E) ⊆ V) (hg : Graph E) (hf6 : fan6 x V E)
    (hx : ∀ e ∈ E, x ∉ e) :
    (fan7 x V E ↔
      ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) := by
  constructor
  · intro h7 e1 he1 e2 he2 hemp
    have h := h7 e1 (by simpa only [p11w_img_singleton_eq] using he1)
      e2 (by simpa only [p11w_img_singleton_eq] using he2)
    rw [h, hemp, P11W_AFFGE_EMPTY]
  · intro h0
    exact p11w2_fan7_of_empty_cond x V E hg
      (fun e he z hz => hun (Set.subset_sUnion_of_mem he hz)) hx h0

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

/-! ### W7 perimeter kit (`p7w3_*` private helpers; WSEWPCH wave W7)

Renders the generic sum-manipulation moves of HOL
`Polar_fan.FAN_PERIMETER_INVARIANT` (polar_fan.hl:2122-2170): the orbit
cycle data comes from the w6a kit (`w6a_orbit_cycle` / `w6a_iter_rho_card`),
`sum 0..k-1` reindexing `i ↦ (i + m) MOD k` is `Finset.sum_nbij'` on the
`Nat` mod window lemmas below. -/

section W7Kit

/-- `k`-periodic point: every orbit point of `x` is again `k`-periodic
(HOL `ITER_ADD` move `ITER k (rho) (ITER j (rho) v) = ITER j (rho) v`). -/
private theorem p7w3_period_all {α : Type*} (f : α → α) {x : α} {k : ℕ}
    (hx : f^[k] x = x) (j : ℕ) : f^[k] (f^[j] x) = f^[j] x := by
  rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hx]

/-- Periodic sequences: shifting the argument by `k * q` changes nothing
(HOL `SUM_OFFSET`/`ITER_ADD`-flavoured telescope). -/
private theorem p7w3_period_add {k : ℕ} (f : ℕ → ℝ) (hper : ∀ j, f (j + k) = f j)
    (q x : ℕ) : f (x + k * q) = f x := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : x + k * (q + 1) = (x + k * q) + k := by ring
    rw [hsplit, hper, ih]

/-- `n % k` on the window `k ≤ n < 2 * k`. -/
private theorem p7w3_mod_twok {k n : ℕ} (h1 : k ≤ n) (h2 : n < k + k) :
    n % k = n - k := by
  have h : (n - k + 1 * k) % k = (n - k) % k :=
    Nat.add_mul_mod_self_right (x := n - k) (y := 1) (z := k)
  have heq : (n - k + k) % k = (n - k) % k := by
    have h2' : n - k + k = n - k + 1 * k := by ring_nf
    rw [h2', h]
  rw [show n % k = (n - k + k) % k from by congr 1; omega, heq,
    Nat.mod_eq_of_lt (by omega)]

/-- Cyclic reindexing of a `k`-periodic sum: shifting by `m < k` inside a
`range k` sum is the identity.  This is the `SUM_EQ_GENERAL` move on
`\i. (i + m) MOD k` in HOL `FAN_PERIMETER_INVARIANT`
(polar_fan.hl:2153-2170, with `MOD_UNIQ`/`DIVISION` discharged by the
`Nat` window lemmas above). -/
private theorem p7w3_sum_mod_shift {k m : ℕ} (hk : 0 < k) (hmk : m < k) (f : ℕ → ℝ)
    (hper : ∀ j, f (j + k) = f j) :
    ∑ i ∈ Finset.range k, f (i + m) = ∑ i ∈ Finset.range k, f i := by
  have step1 : ∑ i ∈ Finset.range k, f (i + m)
      = ∑ i ∈ Finset.range k, f ((i + m) % k) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Nat.mod_add_div (i + m) k]
    rw [p7w3_period_add f hper ((i + m) / k) ((i + m) % k)]
  have step2 : ∑ i ∈ Finset.range k, f ((i + m) % k)
      = ∑ i ∈ Finset.range k, f i := by
    refine Finset.sum_nbij' (fun i => (i + m) % k) (fun j => (j + k - m) % k)
      ?_ ?_ ?_ ?_ (fun i _ => rfl)
    · intro i hi
      simp only [Finset.mem_range] at *
      exact Nat.mod_lt _ hk
    · intro j hj
      simp only [Finset.mem_range] at *
      exact Nat.mod_lt _ hk
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      rcases Nat.lt_or_ge (i + m) k with hlt | hge
      · have hs : (i + m) % k = i + m := Nat.mod_eq_of_lt hlt
        have hik : (i + m) % k + k - m = i + k := by rw [hs]; omega
        have hml : (i + 1 * k) % k = i % k :=
          Nat.add_mul_mod_self_right (x := i) (y := 1) (z := k)
        rw [hik, show i + k = i + 1 * k from by ring, hml, Nat.mod_eq_of_lt hi]
      · have hs : (i + m) % k = i + m - k := p7w3_mod_twok hge (by omega)
        have hik : (i + m) % k + k - m = i := by rw [hs]; omega
        rw [hik, Nat.mod_eq_of_lt hi]
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      rcases Nat.lt_or_ge j m with hlt | hge
      · have ht : (j + k - m) % k = j + k - m := Nat.mod_eq_of_lt (by omega)
        have hjk : (j + k - m) % k + m = j + k := by rw [ht]; omega
        have hml : (j + 1 * k) % k = j % k :=
          Nat.add_mul_mod_self_right (x := j) (y := 1) (z := k)
        rw [hjk, show j + k = j + 1 * k from by ring, hml, Nat.mod_eq_of_lt hj]
      · have ht : (j + k - m) % k = j - m := by
          have h1 : j + k - m = (j - m) + 1 * k := by omega
          have h2 : j - m < k := by omega
          have hml : ((j - m) + 1 * k) % k = (j - m) % k :=
            Nat.add_mul_mod_self_right (x := j - m) (y := 1) (z := k)
          rw [h1, hml, Nat.mod_eq_of_lt h2]
        have hjk : (j + k - m) % k + m = j := by rw [ht]; omega
        rw [hjk, Nat.mod_eq_of_lt hj]
  rw [step1, step2]

/-- Orbit-index bijection `i ↦ ITER i (rho_node1) v` between `range p` and
`V` (content of HOL `Local_lemmas1.LT_CARD_MONO_LOFA` /
`POINT_PRESENTED_IN_RHOND1`, consumed by `FAN_PERIMETER`). -/
private theorem p7w3_orbit_surj {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) {p : ℕ}
    (hcover : ({(rhoNode1_p2 FF)^[n] v | n < p} : Set V3) = V) :
    ∀ b ∈ V, ∃ n, n < p ∧ (rhoNode1_p2 FF)^[n] v = b := by
  intro b hb
  rw [← hcover] at hb
  obtain ⟨n, hn, hnb⟩ := hb
  exact ⟨n, Set.mem_Iio.mp hn, hnb⟩

end W7Kit

/-- HOL `FAN_PERIMETER_INVARIANT` (polar_fan.hl:2122). -/
theorem FAN_PERIMETER_INVARIANT {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) :
    fanPerimeter V E FF =
      ∑ i ∈ Finset.range ((FF.ncard - 1 : ℕ) + 1),
        arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) := by
  have h2 : localFan_p2 V E FF := w6a_to_p2 h hedge
  have hcard : FF.ncard = V.ncard := LOFA_IMP_CARD_FF_V_EQ h2
  have hv0 : 0 < V.ncard := w6a_vcard_pos h2 hv
  -- unfold the perimeter definition; the epsilon point lands on the orbit of `v`
  have h0 : fanPerimeter V E FF =
      ∑ i ∈ Finset.range ((FF.ncard - 1 : ℕ) + 1),
        arcV (0 : V3) ((rhoNode1 FF)^[i] (Classical.epsilon (fun z : V3 => z ∈ V)))
          ((rhoNode1 FF)^[i + 1] (Classical.epsilon (fun z : V3 => z ∈ V))) := rfl
  rw [h0]
  have hwV : (Classical.epsilon (fun z : V3 => z ∈ V)) ∈ V :=
    Classical.epsilon_spec (p := fun z : V3 => z ∈ V) ⟨v, hv⟩
  obtain ⟨m, hmk, hmwe⟩ := LOCAL_FAN_ORBIT_MAP_EXPLICIT_LA7 h hedge v _ hv hwV
  rw [hmwe, show ((FF.ncard - 1 : ℕ) + 1) = V.ncard from by rw [hcard]; omega]
  simp only [← Function.iterate_add_apply, Nat.add_right_comm]
  -- the orbit-indexed summand is `V.ncard`-periodic
  have hK : ∀ n : ℕ, (rhoNode1 FF)^[n + V.ncard] v = (rhoNode1 FF)^[n] v := by
    intro n
    rw [Nat.add_comm, Function.iterate_add_apply, p7w3_period_all (rhoNode1 FF)
      (w6a_iter_rho_card h2 hv) n]
  have hper : ∀ j : ℕ,
      (fun i => arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v))
          (j + V.ncard)
        = (fun i => arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v)) j := by
    intro j
    simp only
    rw [hK j, show j + V.ncard + 1 = (j + 1) + V.ncard from by ring, hK (j + 1)]
  exact p7w3_sum_mod_shift hv0 hmk
    (fun i => arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v)) hper

/-- HOL `FAN_PERIMETER_INVARIANT_CARD_V` (polar_fan.hl:2171). -/
theorem FAN_PERIMETER_INVARIANT_CARD_V {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) :
    fanPerimeter V E FF =
      ∑ i ∈ Finset.range ((V.ncard - 1 : ℕ) + 1),
        arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) := by
  rw [FAN_PERIMETER_INVARIANT h hedge v hv, LOFA_IMP_CARD_FF_V_EQ (w6a_to_p2 h hedge)]

/-- HOL `FAN_PERIMETER` (polar_fan.hl:2184). -/
theorem FAN_PERIMETER {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    fanPerimeter V E FF = setSum V (fun v : V3 => arcV (0 : V3) v (rhoNode1 FF v)) := by
  have h2 : localFan_p2 V E FF := w6a_to_p2 h hedge
  obtain ⟨d, hdFF⟩ : FF.Nonempty := Set.nonempty_iff_ne_empty.mpr (LOCAL_FAN_NOT_EMPTY_FF h)
  have hv : d.1 ∈ V := (WRGCVDR_BIJ h2).1 hdFF
  obtain ⟨p, hp0, hpx, hdis, hcover, hcard⟩ :=
    w6a_orbit_cycle (fun z hz => WRGCVDR_ORBIT h2 z hz) hv
  have hVfin : V.Finite := by
    have himg : ((fun n : ℕ => (rhoNode1_p2 FF)^[n] d.1) '' Set.Iio p : Set V3)
        = V := rfl.trans hcover
    rw [← himg]
    exact (Set.finite_Iio p).image (fun n : ℕ => (rhoNode1_p2 FF)^[n] d.1)
  rw [FAN_PERIMETER_INVARIANT_CARD_V h hedge d.1 hv, hcard,
    show p - 1 + 1 = p from by omega]
  rw [setSum, dif_pos hVfin]
  refine Finset.sum_nbij (fun i => (rhoNode1_p2 FF)^[i] d.1) ?_ ?_ ?_ ?_
  · intro i _
    exact (Set.Finite.mem_toFinset hVfin).mpr (w6a_iter_rho_mem h2 hv i)
  · intro i hi j hj hcon
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hcon (hdis i j hlt hj)
    · exact heq
    · exact absurd hcon.symm (hdis j i hgt hi)
  · intro b hb
    have hbV : b ∈ V := (Set.Finite.mem_toFinset hVfin).mp hb
    obtain ⟨n, hn, hnb⟩ := p7w3_orbit_surj h2 hv hcover b hbV
    exact ⟨n, Finset.mem_range.mpr hn, hnb⟩
  · intro i _
    rw [Function.iterate_succ_apply']
    rfl

/-! ### W8 assembly kit (hedge extraction + WSEWPCH core; WSEWPCH wave W8)

Two encoding-level bridges completing the perimeter lane's consumption
surface for the `yk11` route (`yk11_perimeterBound_of_core`, TameLp):

1. `LOCAL_FAN_IMP_HEDGE` — the SF-54 delta: LA1 `LocalFan` carries
   `∀ u ∈ V, (ee u E).ncard = 2` (`ee v E = {w | {v, w} ∈ E}`, localization
   `EE`), so the hedge hypothesis that HOL `local_fan` packages internally
   is *provable* here and no longer needs to be threaded as an assumption
   downstream.
2. `WSEWPCH_CORE` — the yk11 hcore master (`yk11_WSEWPCH_core` of the
   roadmap, `docs/hf-proof-map.md` §5 second root): the face-sum statement
   `∀ U E' g, ConvexLocalFan U E' g → setSum g (arcV 0 d.1 d.2) ≤ 2*π`,
   derived from the perimeter bound (= the `WSEWPCH` statement shape) via
   `FAN_PERIMETER` and the dart↔vertex reindex along `WRGCVDR_BIJ`.
   Final assembly at body-closure is the single line `WSEWPCH_CORE WSEWPCH`.
3. `FAN_PERIMETER_LE_2PI_OF_CARD_LE` — the `CARD V ≤ 2` branch of the
   WSEWPCH induction (polar_fan.hl:2633-2648) as a standalone real lemma:
   each summand is `arcV ≤ π` (`arcV = Real.arccos …`, so the HOL
   `ARCV_BOUNDS` content is one `Real.arccos_le_pi` here — no LA6 import
   needed) and the orbit sum has ≤ 2 terms. -/

/-- The hedge hypothesis is derivable from `LocalFan`: every vertex has
exactly two neighbours (`ee v E = {w | {v, w} ∈ E}`, the localization `EE`),
so `{v, w} ∈ E` for some `w`.  This discharges the SF-54 "isolated vertex"
note: LA1 `LocalFan` cannot have `V`-vertices without edges. -/
theorem LOCAL_FAN_IMP_HEDGE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  obtain ⟨hfan, x, hxd, hFF, hD, hee⟩ := h
  intro v hv
  have h2 : (ee v E).ncard = 2 := hee v hv
  rcases Set.eq_empty_or_nonempty (ee v E) with h0 | hne
  · rw [h0] at h2
    simp at h2
  · obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw⟩

/-- **WSEWPCH core** (yk11 hcore master).  The hypothesis is exactly the
`WSEWPCH` statement shape (perimeter bound of a convex local fan); the
conclusion is the face-sum form consumed by
`yk11_perimeterBound_of_core` (TameLp).  Assembly once the WSEWPCH body
is real: `WSEWPCH_CORE WSEWPCH`. -/
theorem WSEWPCH_CORE
    (hW : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      ConvexLocalFan V E FF → (∀ v ∈ V, ∃ w, {v, w} ∈ E) →
        fanPerimeter V E FF ≤ 2 * Real.pi)
    (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3))
    (hcl : ConvexLocalFan U E' g) :
    setSum g (fun d : V3 × V3 => arcV (0 : V3) d.1 d.2) ≤ 2 * Real.pi := by
  have hed : ∀ v ∈ U, ∃ w, {v, w} ∈ E' := LOCAL_FAN_IMP_HEDGE hcl.1
  have h2 : localFan_p2 U E' g := w6a_to_p2 hcl.1 hed
  have hbij := WRGCVDR_BIJ h2
  obtain ⟨hfan, x, hxd, hFF, hD, hee⟩ := hcl.1
  have hsub : g ⊆ dart1OfFan U E' := by
    rw [hFF]
    exact (orbitMap_subset_of_permutesOn (hypermapOfFan 0 U E' hfan).faceMap_permutes hxd).trans
      (p7w2_coe_darts hfan).subset
  have hGfin : g.Finite := (finite_dart1_fan hfan).subset hsub
  have hUfin : U.Finite := Set.BijOn.image_eq hbij ▸ hGfin.image Prod.fst
  -- dart-sum reindexes to the vertex-sum (fst is a bijection FF → V)
  have hreindex : setSum g (fun d : V3 × V3 => arcV (0 : V3) d.1 d.2)
      = setSum U (fun v : V3 => arcV (0 : V3) v (rhoNode1 g v)) := by
    rw [setSum, setSum, dif_pos hGfin, dif_pos hUfin]
    refine Finset.sum_nbij (fun d => d.1) ?_ ?_ ?_ ?_
    · intro d hd
      exact (Set.Finite.mem_toFinset hUfin).mpr
        (hbij.1 ((Set.Finite.mem_toFinset hGfin).mp hd))
    · intro d hd e he hcon
      exact hbij.2.1 ((Set.Finite.mem_toFinset hGfin).mp hd)
        ((Set.Finite.mem_toFinset hGfin).mp he) hcon
    · intro v hv
      obtain ⟨d, hd, hd1⟩ := hbij.2.2 ((Set.Finite.mem_toFinset hUfin).mp hv)
      exact ⟨d, (Set.Finite.mem_toFinset hGfin).mpr hd, hd1⟩
    · intro d hd
      rw [← w6a_deter h2 ((Set.Finite.mem_toFinset hGfin).mp hd)]
      rfl
  calc setSum g (fun d : V3 × V3 => arcV (0 : V3) d.1 d.2)
      = setSum U (fun v : V3 => arcV (0 : V3) v (rhoNode1 g v)) := hreindex
    _ = fanPerimeter U E' g := (FAN_PERIMETER hcl.1 hed).symm
    _ ≤ 2 * Real.pi := hW U E' g hcl hed

/-- `arcV` is an arccos, so the HOL `ARCV_BOUNDS` content (`arcV ≤ π`) is
immediate; kept private to avoid clashing LA6's public `ARCV_BOUNDS`. -/
private theorem p8w_arcV_le_pi (u v w : V3) : arcV u v w ≤ Real.pi :=
  Real.arccos_le_pi _

/-- The `CARD V ≤ 2` branch of the WSEWPCH induction
(polar_fan.hl:2633-2648) as a standalone lemma: the orbit sum has at most
two terms, each bounded by `π`. -/
theorem FAN_PERIMETER_LE_2PI_OF_CARD_LE {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : ConvexLocalFan V E FF)
    (hed : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hcard : V.ncard ≤ 2) :
    fanPerimeter V E FF ≤ 2 * Real.pi := by
  have h2 : localFan_p2 V E FF := w6a_to_p2 h.1 hed
  obtain ⟨d0, hd0⟩ : FF.Nonempty := Set.nonempty_iff_ne_empty.mpr (LOCAL_FAN_NOT_EMPTY_FF h.1)
  have hv : d0.1 ∈ V := (WRGCVDR_BIJ h2).1 hd0
  rw [FAN_PERIMETER_INVARIANT h.1 hed d0.1 hv, LOFA_IMP_CARD_FF_V_EQ h2]
  refine le_trans (Finset.sum_le_sum fun i _ => p8w_arcV_le_pi _ _ _) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (t := Finset.range 2) ?_ ?_) ?_
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ _
    exact Real.pi_pos.le
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

/-! ### W9 circular-branch kit (`p9w_*` private helpers; WSEWPCH wave W9)

The downstream half of the WSEWPCH circular branch (polar_fan.hl:2271-2360):
from the KCHMAMG structure (as assembled by LA35's real `KCHMAMG_thm_p35`)
to the 2*pi perimeter bound, via `RHO_NODE1_MONO_WITH_AZIM` (LA5, real),
`ORDER_AZIM_SUM2Pi_0` (this file, real) and `CROSS_POSITIVE_MULTIPLE_AZIM_AXIS`
(this file, real).  The two slots left open by LA35 (the OZQVSFF chain and
`LOFA_V_SUBSET_AFF_HULL`; w6b 件1-3 remain open) are carried as explicit
hypotheses `hplane` / `hint`, mirroring the `KCHMAMG_thm_p35` input face, so
the final one-line assembly reads
`FAN_PERIMETER_LE_2PI_OF_CIRCULAR_STRUCT hcl hed hplane hint`. -/

section W9Kit

/-- 轴的正常数缩放下 `AzimSpec` 不变（HOL `AZIM_SPECIAL_SCALE` 的角色；
`PlanarityAuto8.azimSpec_axis_smul` 的逐字副本，彼件 private 不可 import）。 -/
private theorem p9w_azimSpec_axis_smul {v w u w1 w2 : V3} {θ c : ℝ}
    (hc : 0 < c) (hu : u - v = c • (w - v))
    (hspec : AzimSpec v w w1 w2 θ) :
    AzimSpec v u w1 w2 θ := by
  obtain ⟨hθ0, hθ1, h1, h2, hframes⟩ := hspec
  refine ⟨hθ0, hθ1, h1 / c, h2 / c, ?_⟩
  intro e1 e2 e3 he hax hu_ne
  have hcne : c ≠ 0 := ne_of_gt hc
  have hwv : w ≠ v := by
    intro hwv
    apply hu_ne
    have hzero : u - v = 0 := by rw [hu, hwv, sub_self, smul_zero]
    exact sub_eq_zero.mp hzero
  have hwv_eq : (w - v : V3) = (c⁻¹ * dist u v) • e3 := by
    have hthis : c • (w - v) = dist u v • e3 := by rw [← hu, hax]
    calc (w - v : V3) = c⁻¹ • (c • (w - v)) := by
          rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
      _ = c⁻¹ • (dist u v • e3) := by rw [hthis]
      _ = (c⁻¹ * dist u v) • e3 := by rw [smul_smul]
  have hdist : dist w v = c⁻¹ * dist u v := by
    rw [dist_eq_norm, hwv_eq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hc.le) dist_nonneg)]
    have he3 : ‖e3‖ = 1 := by
      have hsq : ‖e3‖ ^ 2 = 1 := by rw [norm_sq_eq_dot, he.2.2.1]
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact h
      · exfalso; linarith [norm_nonneg e3, h]
    rw [he3, mul_one]
  have hwv_hax : (w - v : V3) = dist w v • e3 := by rw [hwv_eq, hdist]
  obtain ⟨ψ, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframes e1 e2 e3 he hwv_hax hwv
  refine ⟨ψ, r1, r2, ?_, ?_, hr1, hr2⟩
  · rw [hrep1, hu, smul_smul, div_mul_cancel₀ _ hcne]
  · rw [hrep2, hu, smul_smul, div_mul_cancel₀ _ hcne]

/-- 轴心纯量倍不引入共线：`Collinear3 0 (a • e) z ↔ Collinear3 0 e z`
（a ≠ 0；`collinear3_iff_smul` 双向转写）。 -/
private theorem p9w_collinear3_axis_smul {e z : V3} {a : ℝ} (ha : a ≠ 0)
    (hw : e ≠ 0) : Collinear3 0 (a • e) z ↔ Collinear3 0 e z := by
  constructor
  · intro hcol
    by_cases hwz : z = 0
    · rw [hwz]
      exact p7w_col_131 0 e
    · obtain ⟨t, ht⟩ := (collinear3_iff_smul (v := 0) (w := a • e) (w1 := z)
        (smul_ne_zero ha hw)).mp hcol
      exact (collinear3_iff_smul (v := 0) (w := e) (w1 := z) hw).mpr
        ⟨t * a, by simp only [ht, sub_zero, smul_smul]⟩
  · intro hcol
    by_cases hwz : z = 0
    · rw [hwz]
      exact p7w_col_131 0 (a • e)
    · obtain ⟨t, ht⟩ := (collinear3_iff_smul (v := 0) (w := e) (w1 := z) hw).mp hcol
      exact (collinear3_iff_smul (v := 0) (w := a • e) (w1 := z)
        (smul_ne_zero ha hw)).mpr
        ⟨t / a, by simp only [ht, sub_zero, smul_smul, div_mul_cancel₀ _ ha]⟩

/-- 轴向正缩放不改变方位角（HOL `AZIM_SPECIAL_SCALE` 的消费形）。 -/
private theorem p9w_azim_axis_smul {e u w1 w2 : V3} {a : ℝ} (ha : 0 < a)
    (hu : u = a • e) : azim 0 u w1 w2 = azim 0 e w1 w2 := by
  have hcne : a ≠ 0 := ne_of_gt ha
  have hct : ∀ z : V3, Collinear3 0 u z ↔ Collinear3 0 e z := by
    intro z
    by_cases hw : e = 0
    · subst hw
      have hu0 : u = 0 := by rw [hu, smul_zero]
      subst hu0
      exact Iff.rfl
    · rw [hu]
      exact p9w_collinear3_axis_smul hcne hw
  by_cases h1c : Collinear3 0 e w1
  · have h1u : Collinear3 0 u w1 := (hct w1).mpr h1c
    unfold azim
    rw [if_pos (Or.inl h1u), if_pos (Or.inl h1c)]
  · by_cases h2c : Collinear3 0 e w2
    · have h2u : Collinear3 0 u w2 := (hct w2).mpr h2c
      unfold azim
      rw [if_pos (Or.inr h2u), if_pos (Or.inr h2c)]
    · have hn1 : ¬ Collinear3 0 u w1 := fun hcon => h1c ((hct w1).mp hcon)
      have hn2 : ¬ Collinear3 0 u w2 := fun hcon => h2c ((hct w2).mp hcon)
      have hspecE : AzimSpec 0 e w1 w2 (azim 0 e w1 w2) := by
        have hnd : ¬ (Collinear3 0 e w1 ∨ Collinear3 0 e w2) := by tauto
        unfold azim
        rw [if_neg hnd]
        exact Classical.epsilon_spec (azimSpec_exists h1c h2c)
      exact azim_eq_of_spec hn1 hn2
        (p9w_azimSpec_axis_smul ha (by rw [hu, sub_zero, sub_zero]) hspecE)

/-- 轴向纯量倍点落在 `{0, a}` 的仿射包里（HOL `AFFINE_HULL_2` 过 0 特款；
LA35 `kchSmulMemAffSpanZero_p35` 的逐字副本，彼件 private）。 -/
private theorem p9w_smul_mem_affineSpan_zero (a : V3) (c : ℝ) :
    c • a ∈ affineSpan ℝ ({0, a} : Set V3) := by
  show c • a ∈ (affineSpan ℝ (insert 0 ({a} : Set V3)) : Set V3)
  rw [affineSpan_insert_zero]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton a))

/-- **CYCLIC_SET_IMP_NOT_COLLINEAR 面**（Wrgcvdr_cizmrrh，KCHMAMG :3394 消费；
LA35 `kchNotCollinear3_of_cyclicSet_p35` 的逐字副本，彼件 private）。 -/
private theorem p9w_notCollinear3_of_cyclicSet {W : Set V3} {e x : V3}
    (hcy : cyclicSet_p3 W 0 e) (hx : x ∈ W) : ¬ Collinear3 0 e x := by
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := e) (w1 := x)
    (Ne.symm hcy.1)).mp hcol
  have hxm : x ∈ affineSpan ℝ ({0, e} : Set V3) := by
    have h1 : x - 0 = c • (e - 0) := hc
    simp only [sub_zero] at h1
    rw [h1]
    exact p9w_smul_mem_affineSpan_zero e c
  have hmem : x ∈ W ∩ (affineSpan ℝ ({0, e} : Set V3) : Set V3) := Set.mem_inter hx hxm
  have hmem2 : x ∈ (∅ : Set V3) := hcy.2.2.2 ▸ hmem
  exact absurd hmem2 (by simp)

/-- V3 加法经强制转换保形（LA35 `kchCoeAdd_p35` 同款）。 -/
private theorem p9w_coe_addP (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = ((a : V3) : Fin 3 → ℝ) + ((b : V3) : Fin 3 → ℝ) := rfl

/-- azim = 0 的导渲染（LA35 `pmAzimNormalRender0_p35` 逐字副本，彼件 private）：
`azim 0 ax a x = 0` 把目标放在开参考射线加轴松弛上（`x = e • ax + c • a`，
c > 0）。 -/
private theorem p9w_azim_zero_render {ax a x : V3} (ha0 : a ≠ (0:V3))
    (hnc : ¬ Collinear3 0 ax a) (hncx : ¬ Collinear3 0 ax x)
    (h : azim 0 ax a x = 0) :
    ∃ e c : ℝ, 0 < c ∧ x - 0 = e • (ax - 0) + c • (a - 0) := by
  obtain ⟨c, hc, e, he⟩ :=
    (affGt_pair_iff (v0 := (0:V3)) (v1 := ax) (x := a) (y := x)
      (fun hz => hnc (by rw [hz]; exact collinear3_of_eq rfl))
      ha0 (fun hz => hnc (by rw [hz]; exact collinear3_pair_right rfl))).mp
    ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := ax) (w := a) (x := x) hnc hncx).mp h)
  exact ⟨e, c, hc, by rw [he]; exact add_comm _ _⟩

end W9Kit

/-- **WSEWPCH circular 支下游半程**（polar_fan.hl:2271-2360 独立形）：凸局部扇
+ 圆结构输入面（`hplane` = V 落在过 0 平面，`hint` = 全体顶点内角平角——
即 LA35 `KCHMAMG_thm_p35` 的两枚显式输入槽；其上游 = OZQVSFF 链与
`LOFA_V_SUBSET_AFF_HULL`，见 w6b 件1-3 与独立波）⟹ 周长 ≤ 2π。
装配链（对 HOL 逐行忠实）：`KCHMAMG_thm_p35` 给轴 `e` ⊥ V 与
`azim 0 e v (ρv) = arcV < π`；`CROSS_POSITIVE_MULTIPLE_AZIM_AXIS` 给
`cross3 v (ρv) = a • e`（a > 0），轴向缩放传输正交/非共线/方位角到
`cross3 v (ρv)`；`RHO_NODE1_MONO_WITH_AZIM`（LA5）给轨道单调；
`ORDER_AZIM_SUM2Pi_0` 收口 `∑ azim = 2π`，而 `fanPerimeter`（W7 不变量）
逐项等于该和。 -/
theorem FAN_PERIMETER_LE_2PI_OF_CIRCULAR_STRUCT {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (hcl : ConvexLocalFan V E FF)
    (hed : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hplane : ∃ P : Set V3,
      (∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧
        P = affineSpan ℝ ({u, v, w} : Set V3)) ∧ (0:V3) ∈ P ∧ V ⊆ P)
    (hint : ∀ v ∈ V, interiorAngle1 0 FF v = Real.pi) :
    fanPerimeter V E FF ≤ 2 * Real.pi := by
  obtain ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩ := hcl.1
  have hcl' : LocalFan V E FF := ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl' hed
  have hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2 := fun u hu => hee u hu
  obtain ⟨hint', A, hplaneA, h0A, hVA, e, heA, hcyc, hvc⟩ :=
    KCHMAMG_thm_p35 ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩ hEE2 hplane hint
  obtain ⟨uP, vP, wP, hncP, hdefP⟩ := hplaneA
  have hP2 : plane_p2 A := ⟨uP, vP, wP, hncP, hdefP⟩
  -- base vertex from a dart
  obtain ⟨d0, hd0⟩ : FF.Nonempty := Set.nonempty_iff_ne_empty.mpr
    (LOCAL_FAN_NOT_EMPTY_FF ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩)
  have hv0 : d0.1 ∈ V := (WRGCVDR_BIJ h2).1 hd0
  have hv0cl := hvc d0.1 hv0
  have hmem : ∀ i : ℕ, (rhoNode1 FF)^[i] d0.1 ∈ V := w6a_iter_rho_mem h2 hv0
  -- non-collinearity of {0, e, z} for all z ∈ V
  have hncE : ∀ z ∈ V, ¬ Collinear ℝ ({(0:V3), e, z} : Set V3) :=
    fun z hz => p9w_notCollinear3_of_cyclicSet hcyc hz
  have he0 : e ≠ 0 := by
    intro hz
    refine hncE (rhoNode1 FF d0.1) (hmem 1) ?_
    subst hz
    exact collinear3_of_eq (v := 0) (w := 0) rfl
  -- azim at the base vertex is strictly positive (render route: azim = 0 would
  -- put ρv0 in span{e, v0} with zero e-component, hence ρv0 ∥ v0 — CHARACTER2)
  have hv0ne : d0.1 ≠ 0 := fun hz =>
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv0 (by rw [hz]; exact collinear3_of_eq rfl)
  have hpos : 0 < azim 0 e d0.1 (rhoNode1 FF d0.1) := by
    refine lt_of_le_of_ne (azim_nonneg 0 e d0.1 (rhoNode1 FF d0.1)) (Ne.symm ?_)
    intro hz0
    obtain ⟨e', c', hc'0, hx'⟩ :=
      p9w_azim_zero_render (ax := e) (a := d0.1) (x := rhoNode1 FF d0.1) hv0ne
        (hncE d0.1 hv0) (hncE (rhoNode1 FF d0.1) (hmem 1)) hz0
    have hx'' : rhoNode1 FF d0.1 = e' • e + c' • d0.1 := by
      simpa using hx'
    have hdot : ((rhoNode1 FF d0.1 : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]
      exact heA _ (hVA (hmem 1))
    have hdotv : ((d0.1 : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]
      exact heA _ (hVA hv0)
    have hcongr : e' * (((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ)) = 0 := by
      have h := congrArg
        (fun w : V3 => ((w : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ)) hx''
      simp only [p9w_coe_addP, coe_smulP, add_dotProduct, smul_dotP] at h
      rw [hdot, hdotv, mul_zero, add_zero] at h
      exact h.symm
    have hee : (0:ℝ) < ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) := by
      have hn : (0:ℝ) < ‖e‖ := norm_pos_iff.mpr he0
      have h2' : (0:ℝ) < ‖e‖ ^ 2 := by positivity
      rwa [norm_sq_eq_dot, p7w_dot_coe] at h2'
    have he'0 : e' = 0 := by
      rcases mul_eq_zero.mp hcongr with h | h
      · exact h
      · linarith [hee, h]
    have hpar : rhoNode1 FF d0.1 = c' • d0.1 := by
      rw [he'0] at hx''
      simpa using hx''
    exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv0
      ((collinear3_iff_smul (v := 0) (w := d0.1) (w1 := rhoNode1 FF d0.1) hv0ne).mpr
        ⟨c', by rw [hpar, sub_zero, sub_zero]⟩)
  -- the rho orbit axis equals a positive multiple of the KCHMAMG axis
  obtain ⟨a, ha0, hcpl⟩ :=
    CROSS_POSITIVE_MULTIPLE_AZIM_AXIS he0
      (by rw [p7w_dot_coe]; exact heA d0.1 (hVA hv0))
      (by rw [p7w_dot_coe]; exact heA _ (hVA (hmem 1)))
      hpos hv0cl.2.2.2
  -- transport non-collinearity to the cross axis
  have hcnc : ∀ z ∈ V,
      ¬ Collinear ℝ ({(0:V3), cross3 d0.1 (rhoNode1 FF d0.1), z} : Set V3) :=
    fun z hz hcon =>
      hncE z hz ((p9w_collinear3_axis_smul (ne_of_gt ha0) he0).mp (hcpl ▸ hcon))
  -- cross3 as the RHO_NODE1_MONO axis (WithLp transport)
  have hcroe : (WithLp.toLp 2 (crossProduct ((d0.1 : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF d0.1 : V3) : Fin 3 → ℝ)) : V3)
      = cross3 d0.1 (rhoNode1 FF d0.1) := by
    refine p7w_v3_eq ?_
    rw [coe_toLp, coe_cross3P]
    rfl
  set g : ℕ → V3 := fun i => (rhoNode1 FF)^[i] d0.1 with hge
  have hge2 : 2 ≤ V.ncard := by
    have hge3 := LOCAL_FAN_NOT_CARD_FF_GE_2 hcl'
    rw [LOFA_IMP_CARD_FF_V_EQ h2] at hge3
    exact hge3
  have hncard : (V.ncard - 1 : ℕ) + 1 = V.ncard := by omega
  have hper : ∀ n : ℕ, (rhoNode1 FF)^[n + V.ncard] d0.1 = (rhoNode1 FF)^[n] d0.1 := by
    intro n
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact p7w3_period_all (rhoNode1 FF) (w6a_iter_rho_card h2 hv0) n
  -- orbit monotonicity around the cross axis (LA5 real)
  have hmono := RHO_NODE1_MONO_WITH_AZIM h2 hv0
    (l := V.ncard - 1)
    (U := {(rhoNode1_p2 FF)^[n] d0.1 | n ≤ V.ncard - 1})
    (rfl) hP2 h0A
    (fun z hz => by
      obtain ⟨n, hn, rfl⟩ := hz
      exact hVA (hmem n))
    hcroe
  -- ORDER_AZIM_SUM2Pi_0 instance
  have hsum := ORDER_AZIM_SUM2Pi_0
    (x := 0) (y := cross3 d0.1 (rhoNode1 FF d0.1)) (z := d0.1) (n := V.ncard - 1)
    (g := g)
    (by exact hcnc d0.1 hv0)
    (fun i hi => by
      simp only [Finset.mem_Ico, Finset.mem_range] at hi
      exact hcnc (g i) (hmem i))
    (by show (rhoNode1 FF)^[((V.ncard - 1 : ℕ) + 1)] d0.1 = (rhoNode1 FF)^[0] d0.1
        rw [hncard]
        have h0 := hper 0
        rwa [Nat.zero_add] at h0)
    (by omega)
    (fun j hj k hk hjk => by
      simp only [Finset.mem_Ico, Finset.mem_range] at hj hk
      exact hmono j k hjk (by omega) (by omega))
  -- the perimeter sum rewrites into the ORDER sum pointwise
  refine le_of_eq ?_
  rw [FAN_PERIMETER_INVARIANT ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩ hed d0.1 hv0,
    LOFA_IMP_CARD_FF_V_EQ h2]
  have hIco : (Finset.Ico 0 ((V.ncard - 1 : ℕ) + 1) : Finset ℕ)
      = Finset.range ((V.ncard - 1 : ℕ) + 1) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_range]
    omega
  rw [hIco] at hsum
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
  rw [p9w_azim_axis_smul ha0 hcpl]
  simp only [hge]
  rw [Function.iterate_succ_apply']
  exact (hvc ((rhoNode1 FF)^[i] d0.1) (hmem i)).2.2.1.symm

/-! ### W10 lunar-branch kit (`p10w_*` private helpers; WSEWPCH wave W10)

The lunar branch (polar_fan.hl:2360-2537): the lunar fan splits the rho orbit
into two half-cycles (`w → v` in `n` steps and `v → w` in `m` steps); each
half telescopes (via `Fan.sum4_azim_fan` + `RHO_NODE1_MONO_WITH_AZIM`) to an
endpoint azimuth lying on the lunar line `{0, v, w}`, hence ≤ π.

`W10a` proves the telescope core with the half-cycle data as explicit slots
(mirroring the W9 slot architecture): `m n`, the endpoint equations and the
plane memberships (`hplane1/hplane2`, derived in `W10b` from `HKIRPEP`'s arc
equations).  `m + n = V.ncard` is derived internally from the w6a
period/divisibility kit (no LA6 import needed). -/

section W10Kit

/-- V3 加法经强制转换保形（LA35 `kchCoeAdd_p35` 同款，本文件私件）。 -/
private theorem p10w_coe_addP (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = ((a : V3) : Fin 3 → ℝ) + ((b : V3) : Fin 3 → ℝ) := rfl

/-- 望远镜：`∑_{k<n} (f(k+1) - f(k)) = f(n) - f(0)`。 -/
private theorem p10w_sum_range_telescope (f : ℕ → ℝ) :
    ∀ n : ℕ, (∑ k ∈ Finset.range n, (f (k + 1) - f k)) = f n - f 0
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, p10w_sum_range_telescope f n]
    ring

/-- **Lunar half-cycle telescope**：基点 `b` 的轨道前 `p` 步之和（`arcV` 口径）
等于端点沿轴 `cross3 b (ρb)` 的方位角，且 ≤ π。 输入面：轨道点全在平面
`{0,b,ρb}`（`hplane`）且端点落在 `{0,b}` 的直线上（`hcol`）。 -/
private theorem p10w_half_sum {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h2 : localFan_p2 V E FF) {b e : V3} (hb : b ∈ V) {p : ℕ} (hp0 : 0 < p)
    (hpV : p < V.ncard) (hend : (rhoNode1 FF)^[p] b = e)
    (hcol : Collinear ℝ ({(0:V3), b, e} : Set V3))
    (hperp : ∀ k : ℕ, k ≤ p →
      (cross3 b (rhoNode1 FF b)) ⬝ᵥ ((rhoNode1 FF)^[k] b) = 0)
    (hplane : ∀ k : ℕ, k ≤ p →
      (rhoNode1 FF)^[k] b ∈ affineSpan ℝ ({(0:V3), b, rhoNode1 FF b} : Set V3)) :
    (∑ k ∈ Finset.range p,
        arcV (0:V3) ((rhoNode1 FF)^[k] b) ((rhoNode1 FF)^[k + 1] b)) ≤ Real.pi := by
  have hmem : ∀ k : ℕ, (rhoNode1 FF)^[k] b ∈ V := w6a_iter_rho_mem h2 hb
  have hnc0 : ¬ Collinear ℝ ({(0:V3), b, rhoNode1 FF b} : Set V3) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hb
  have haxtolp : (WithLp.toLp 2 (crossProduct ((b : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF b : V3) : Fin 3 → ℝ)) : V3) = cross3 b (rhoNode1 FF b) := by
    refine p7w_v3_eq ?_
    rw [coe_toLp, coe_cross3P]
    rfl
  have haxne : cross3 b (rhoNode1 FF b) ≠ 0 := by
    intro hz
    refine hnc0 (COLLINEAR_CROSS_0.mpr ?_)
    have hcoe : (WithLp.toLp 2 (crossProduct ((b - 0 : V3) : Fin 3 → ℝ)
        ((rhoNode1 FF b - 0 : V3) : Fin 3 → ℝ)) : V3) = cross3 b (rhoNode1 FF b) := by
      refine p7w_v3_eq ?_
      rw [coe_toLp, coe_subP, coe_subP, coe_zeroV, sub_zero, sub_zero, coe_cross3P]
    rw [hcoe, hz]
  -- per-term non-collinearity {0, axis, orbit point}
  have hcnc : ∀ k : ℕ, k ≤ p →
      ¬ Collinear3 0 (cross3 b (rhoNode1 FF b)) ((rhoNode1 FF)^[k] b) := by
    intro k hk hcon
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := cross3 b (rhoNode1 FF b))
      (w1 := (rhoNode1 FF)^[k] b) haxne).mp hcon
    have hx : (rhoNode1 FF)^[k] b = c • cross3 b (rhoNode1 FF b) := by
      have hc' := hc
      rw [sub_zero, sub_zero] at hc'
      exact hc'
    have hd : c * ((cross3 b (rhoNode1 FF b)) ⬝ᵥ (cross3 b (rhoNode1 FF b))) = 0 := by
      have h := hperp k hk
      rw [hx] at h
      rw [p7w_dot_coe, p7w_dot_coe, coe_smulP, dotProduct_smul] at h
      rw [p7w_dot_coe]
      exact h
    have haxax : (0:ℝ) < (cross3 b (rhoNode1 FF b)) ⬝ᵥ (cross3 b (rhoNode1 FF b)) := by
      have hn : (0:ℝ) < ‖cross3 b (rhoNode1 FF b)‖ := norm_pos_iff.mpr haxne
      have h2' : (0:ℝ) < ‖cross3 b (rhoNode1 FF b)‖ ^ 2 := by positivity
      rwa [norm_sq_eq_dot] at h2'
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp hd with h | h
      · exact h
      · exact absurd h (ne_of_gt haxax)
    have hx0 : (rhoNode1 FF)^[k] b = 0 := by rw [hx, hc0, zero_smul]
    exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 (hmem k)
      (by rw [hx0]; exact collinear3_of_eq rfl)
  -- orbit monotonicity around the cross axis (LA5 real)
  have hP2p : plane_p2 (affineSpan ℝ ({(0:V3), b, rhoNode1 FF b} : Set V3)) :=
    ⟨0, b, rhoNode1 FF b, hnc0, rfl⟩
  have h0p : (0:V3) ∈ affineSpan ℝ ({(0:V3), b, rhoNode1 FF b} : Set V3) :=
    subset_affineSpan ℝ ({0, b, rhoNode1 FF b} : Set V3) (Set.mem_insert _ _)
  have hmemb : ∀ z ∈ {(rhoNode1_p2 FF)^[n'] b | n' ≤ p},
      z ∈ affineSpan ℝ ({(0:V3), b, rhoNode1 FF b} : Set V3) := by
    intro z hz
    obtain ⟨n', hn', rfl⟩ := hz
    exact hplane n' hn'
  have hmono := RHO_NODE1_MONO_WITH_AZIM h2 hb
    (l := p) (U := {(rhoNode1_p2 FF)^[n'] b | n' ≤ p}) (rfl) hP2p h0p hmemb haxtolp
  set A : ℕ → ℝ := fun k => azim 0 (cross3 b (rhoNode1 FF b)) b ((rhoNode1 FF)^[k] b) with hA
  have hAend : A p = azim 0 (cross3 b (rhoNode1 FF b)) b e := by
    simp only [hA, hend]
  have hA0 : A 0 = 0 := by
    simp only [hA, Function.iterate_zero_apply, azim_self]
  have hAendle : azim 0 (cross3 b (rhoNode1 FF b)) b e ≤ Real.pi := by
    rcases COLLINEAR_AZIM_0_OR_PI 0 (cross3 b (rhoNode1 FF b)) b e hcol with h | h
    · exact le_trans (le_of_eq h) (le_of_lt Real.pi_pos)
    · exact le_of_eq h
  have hAendA : A p ≤ Real.pi := by
    simp only [hA]
    rw [hend]
    exact hAendle
  -- per-term difference identity: azim(ρ^k → ρ^(k+1)) = A(k+1) - A(k)
  have hdiff : ∀ k, k < p →
      azim 0 (cross3 b (rhoNode1 FF b)) ((rhoNode1 FF)^[k] b) ((rhoNode1 FF)^[k + 1] b)
        = A (k + 1) - A k := by
    intro k hk
    have hsum4 := sum4_azim_fan (x := (0:V3)) (v := cross3 b (rhoNode1 FF b)) (u := b)
      (w1 := (rhoNode1 FF)^[k] b) (w2 := (rhoNode1 FF)^[k + 1] b)
      haxne (hcnc 0 (by omega))
      (hcnc k (by omega))
      (hcnc (k + 1) (by omega))
      (by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0, Function.iterate_zero_apply, Function.iterate_one, azim_self]
          exact azim_nonneg _ _ _ _
        · exact (hmono k (k + 1) (by omega) (by omega) (by omega)).le)
    simp only [hA]
    linarith [hsum4]
  -- per-term arcV = A(k+1) - A(k) (AZIM_ARCV with the ≤π bound from monotonicity)
  have hterm : ∀ k, k < p →
      arcV (0:V3) ((rhoNode1 FF)^[k] b) ((rhoNode1 FF)^[k + 1] b) = A (k + 1) - A k := by
    intro k hk
    have hpi : azim 0 (cross3 b (rhoNode1 FF b))
        ((rhoNode1 FF)^[k] b) ((rhoNode1 FF)^[k + 1] b) ≤ Real.pi := by
      have hd := hdiff k hk
      have hAk : A (k + 1) ≤ Real.pi := by
        rcases Nat.lt_or_ge (k + 1) p with hlt | hge
        · exact le_trans (hmono (k + 1) p hlt hpV (le_refl p)).le hAendA
        · have heq : k + 1 = p := by omega
          rw [heq]
          exact hAendA
      have hAk0 : (0:ℝ) ≤ A k := azim_nonneg 0 _ b ((rhoNode1 FF)^[k] b)
      linarith [hd]
    have haeq := AZIM_ARCV (e := cross3 b (rhoNode1 FF b)) (u := (0:V3))
      (v := (rhoNode1 FF)^[k] b) (w := (rhoNode1 FF)^[k + 1] b)
      (by
        show ((cross3 b (rhoNode1 FF b) - 0 : V3) ⬝ᵥ ((rhoNode1 FF)^[k] b - 0 : V3)) = 0
        rw [sub_zero, sub_zero]
        exact hperp k (by omega))
      (by
        show ((cross3 b (rhoNode1 FF b) - 0 : V3)
          ⬝ᵥ ((rhoNode1 FF)^[k + 1] b - 0 : V3)) = 0
        rw [sub_zero, sub_zero]
        exact hperp (k + 1) (by omega))
      (hcnc k (by omega))
      (hcnc (k + 1) (by omega))
      hpi
    rw [← haeq]
    exact hdiff k hk
  calc (∑ k ∈ Finset.range p,
        arcV (0:V3) ((rhoNode1 FF)^[k] b) ((rhoNode1 FF)^[k + 1] b))
      = ∑ k ∈ Finset.range p, (A (k + 1) - A k) :=
        Finset.sum_congr rfl fun k hk => hterm k (Finset.mem_range.mp hk)
    _ = A p - A 0 := p10w_sum_range_telescope A p
    _ = azim 0 (cross3 b (rhoNode1 FF b)) b e - 0 := by rw [hAend, hA0]
    _ ≤ Real.pi := by rw [sub_zero]; exact hAendle

end W10Kit

/-- **WSEWPCH lunar 支**（polar_fan.hl:2360-2537 的望远镜核心独立形）：凸局部扇
+ 两半周数据（`m n`、端点等式、双平面成员——W10b 由 `HKIRPEP` 弧描述 +
`Lunar` 共线派生）⟹ 周长 ≤ 2π。 结构：`m + n = V.ncard`（内部经 w6a 周期
整除导出），`∑_{i<m+n}` 按 `range` 分裂，两个半周各自用
`p10w_half_sum` 望远镜到端点方位角 ≤ π。 -/
theorem FAN_PERIMETER_LE_2PI_OF_LUNAR_STRUCT {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (hcl : ConvexLocalFan V E FF)
    (hed : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hvV : v ∈ V) (hwV : w ∈ V)
    (hcol : Collinear ℝ ({(0:V3), v, w} : Set V3))
    (m n : ℕ) (hn0 : 0 < n) (hm0 : 0 < m)
    (hmV : m < V.ncard) (hnV : n < V.ncard)
    (hvw : v = (rhoNode1 FF)^[n] w) (hwv : w = (rhoNode1 FF)^[m] v)
    (hperp1 : ∀ k : ℕ, k ≤ n →
      (cross3 w (rhoNode1 FF w)) ⬝ᵥ ((rhoNode1 FF)^[k] w) = 0)
    (hperp2 : ∀ k : ℕ, k ≤ m →
      (cross3 v (rhoNode1 FF v)) ⬝ᵥ ((rhoNode1 FF)^[k] v) = 0)
    (hplane1 : ∀ k : ℕ, k ≤ n →
      (rhoNode1 FF)^[k] w ∈ affineSpan ℝ ({(0:V3), w, rhoNode1 FF w} : Set V3))
    (hplane2 : ∀ k : ℕ, k ≤ m →
      (rhoNode1 FF)^[k] v ∈ affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3)) :
    fanPerimeter V E FF ≤ 2 * Real.pi := by
  obtain ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩ := hcl.1
  have hcl' : LocalFan V E FF := ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl' hed
  have hcardpos : 0 < V.ncard := by omega
  have hperw : (rhoNode1 FF)^[V.ncard] w = w := w6a_iter_rho_card h2 hwV
  have hpermn : (rhoNode1 FF)^[m + n] w = w := by
    rw [Function.iterate_add_apply, ← hvw, ← hwv]
  -- V.ncard divides m + n (minimal-period divisibility via the w6a orbit cycle)
  have hpdiv : V.ncard ∣ m + n := by
    have hmod : (rhoNode1 FF)^[(m + n) % V.ncard] w = w := by
      rw [← w6a_period_mod (rhoNode1 FF) hperw (m + n)]
      exact hpermn
    rcases Nat.eq_zero_or_pos ((m + n) % V.ncard) with h0 | hpos
    · exact Nat.dvd_of_mod_eq_zero h0
    · exfalso
      obtain ⟨p', -, -, hdis, -, hcard_eq⟩ :=
        w6a_orbit_cycle (fun z hz => WRGCVDR_ORBIT h2 z hz) hwV
      have hlt : (m + n) % V.ncard < V.ncard := Nat.mod_lt _ hcardpos
      have hltp : (m + n) % V.ncard < p' := by
        rw [← hcard_eq]
        exact hlt
      exact (hdis 0 ((m + n) % V.ncard) hpos hltp)
        (by rw [Function.iterate_zero_apply]; exact hmod.symm)
  have hcard : V.ncard = m + n := by
    obtain ⟨q, hq⟩ := hpdiv
    have hqpos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · rw [hq0, mul_zero] at hq
        omega
      · exact hqpos
    have hqlt : q < 2 := by
      have hlt : V.ncard * q < V.ncard * 2 := by
        rw [← hq]
        omega
      exact Nat.lt_of_mul_lt_mul_left hlt
    have hq1 : q = 1 := by omega
    rw [hq1, mul_one] at hq
    omega
  rw [FAN_PERIMETER_INVARIANT hcl' hed w hwV, LOFA_IMP_CARD_FF_V_EQ h2]
  rw [show (V.ncard - 1 : ℕ) + 1 = V.ncard from by omega, hcard]
  rw [Nat.add_comm m n]
  have hcol' : Collinear ℝ ({(0:V3), w, v} : Set V3) := by
    simpa [Set.pair_comm] using hcol
  have h1half := p10w_half_sum h2 hwV hn0 hnV hvw.symm hcol' hperp1 hplane1
  have h2half : (∑ i ∈ Finset.range m,
      arcV (0:V3) ((rhoNode1 FF)^[n + i] w) ((rhoNode1 FF)^[n + i + 1] w)) ≤ Real.pi := by
    have h := p10w_half_sum h2 hvV hm0 hmV hwv.symm hcol hperp2 hplane2
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (rhoNode1 FF)^[n + i] w = (rhoNode1 FF)^[i] v := by
      rw [Nat.add_comm n i, Function.iterate_add_apply, ← hvw]
    have h2' : (rhoNode1 FF)^[n + i + 1] w = (rhoNode1 FF)^[i + 1] v := by
      rw [show n + i + 1 = (i + 1) + n from by ring]
      rw [Function.iterate_add_apply, ← hvw]
    rw [h1, h2']
  calc (∑ i ∈ Finset.range (n + m),
        arcV (0:V3) ((rhoNode1 FF)^[i] w) ((rhoNode1 FF)^[i + 1] w))
      = (∑ i ∈ Finset.range n,
          arcV (0:V3) ((rhoNode1 FF)^[i] w) ((rhoNode1 FF)^[i + 1] w))
        + (∑ i ∈ Finset.range m,
            arcV (0:V3) ((rhoNode1 FF)^[n + i] w) ((rhoNode1 FF)^[n + i + 1] w)) :=
        Finset.sum_range_add _ n m
    _ ≤ Real.pi + Real.pi := add_le_add h1half h2half
    _ = 2 * Real.pi := by ring


/-! ### W10b lunar slot kit (`p10w_*` continued; WSEWPCH wave W10b)

Slot extraction for `FAN_PERIMETER_LE_2PI_OF_LUNAR_STRUCT` from the real
`HKIRPEP` (LA5:9062):

* `p10w_lunar_data` — `m := i`, `n := j`, positivity / cardinality bounds and
  the two arc equations (the `affGt`-form translations of HOL
  local_lemmas.hl:6027).
* `p10w_lunar_vhalf` — the **v-half** slots: the v-orbit (≤ m steps) lies in
  the plane `{0, v, ρv}` and is orthogonal to the dart axis `cross3 v (ρv)`.
  Endpoints: `k = 0` (v), `k = m` (w, via `Lunar`'s collinearity); interior:
  the arc equation + `AFF_GT_SUB_AFF_UNION` (LA5 real) gives
  `affGt ⊆ affineSpan`; orthogonality then follows from `p10w_affine_perp`
  (the `affineSpan → ⊥` small piece, via `LinearMap.ker` — this replaces the
  `Submodule.span_induction` route that hit the WithLp `x.ofLp` view issue).
* The **w-half** slots (`hperp1`/`hplane1` of the W10a interface) remain
  UNRESOLVED: the w-arc's equation is `affGt {0,v}{ιv} ∩ V`, so the interior
  points live in `span{v, ιv}`; placing them in the W10a plane
  `span{w, ρw}` requires `ιv ∈ span{w, ρw}` — i.e. the lunar-fan planarity
  identity `span{v, ιv} = span{w, ρw}` (HOL's AFFSIGN-mono machinery,
  local_lemmas.hl:2410-2440; not yet ported).  Tracked for W10c.

One-line assembly once W10c lands the w-half slots:
`FAN_PERIMETER_LE_2PI_OF_LUNAR_STRUCT hcl hed hvV hwV hcol m n ...` with the
`m n`/endpoint data from `p10w_lunar_data`, the v-half slots from
`p10w_lunar_vhalf`, and the w-half slots from the W10c planarity piece. -/

section W10bKit

/-- 平面 `{0,a,b}` 上的点与 `a×b` 正交（HOL WSEWPCH 局部 lemma1 的按需形）。
经 `mem_span_pair` 系数形直取：免 `span_induction`/`LinearMap` 的 WithLp 视图
问题（W10a 记档坑的替代路线）。 -/
private theorem p10w_affine_perp {a b x : V3}
    (hx : x ∈ affineSpan ℝ ({(0:V3), a, b} : Set V3)) :
    (cross3 a b) ⬝ᵥ x = 0 := by
  have hx' : x ∈ Submodule.span ℝ ({a, b} : Set V3) := by
    have h := affineSpan_subset_span (k := ℝ) hx
    rw [SetLike.mem_coe] at h
    rwa [show ({(0:V3), a, b} : Set V3) = insert 0 ({a, b} : Set V3) from rfl,
      Submodule.span_insert_zero] at h
  obtain ⟨α, β, hxab⟩ := Submodule.mem_span_pair.mp hx'
  rw [← hxab]
  rw [p7w_dot_coe, p10w_coe_addP, dotProduct_add, coe_smulP, coe_smulP,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have ha : ((cross3 a b : V3) : Fin 3 → ℝ) ⬝ᵥ ((a : V3) : Fin 3 → ℝ) = 0 := by
    rw [coe_cross3P, dotProduct_comm]
    exact dot_self_cross _ _
  have hb : ((cross3 a b : V3) : Fin 3 → ℝ) ⬝ᵥ ((b : V3) : Fin 3 → ℝ) = 0 := by
    rw [coe_cross3P, dotProduct_comm]
    exact dot_cross_self _ _
  rw [ha, hb, mul_zero, mul_zero, add_zero]

/-- lunar 支数据面（`HKIRPEP` 槽位提取）：`m := i`、`n := j`、端点等式与双弧
描述（HOL local_lemmas.hl:6027 的 Lean 形）。 -/
private theorem p10w_lunar_data {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hed : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hlun : Lunar v w V E) :
    ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ m < V.ncard ∧ n < V.ncard ∧
      w = (rhoNode1 FF)^[m] v ∧ v = (rhoNode1 FF)^[n] w ∧
      ((fun l => (rhoNode1 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < m}) =
        (affGt ({0, v} : Set V3) ({rhoNode1 FF v} : Set V3) ∩ V) ∧
      ((fun l => (rhoNode1 FF)^[l] w) '' {l : ℕ | 0 < l ∧ l < n}) =
        (affGt ({0, v} : Set V3) ({ivsRhoNode1 FF v} : Set V3) ∩ V) := by
  obtain ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩ := hcl.1
  have hcl' : LocalFan V E FF := ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl' hed
  have hFFsub : FF ⊆ dart1OfFan V E := by
    rw [hFF0]
    exact (orbitMap_subset_of_permutesOn (hypermapOfFan 0 V E hfanL).faceMap_permutes hxd0).trans
      (p7w2_coe_darts hfanL).subset
  have hcv2 : convexLocalFan_p2 V E FF := by
    refine ⟨h2, fun x hx => ?_⟩
    obtain ⟨haz, hwedge⟩ := hcl.2 x hx
    have hxd : x ∈ dart1OfFan V E := hFFsub hx
    refine ⟨?_, ?_⟩
    · rw [show azimInFan_p2 x E = azimInFan_p3 x E from rfl,
        ← azimInFan_eq_azimInFan_p3 hfanL hxd]
      exact haz
    · rw [show wedgeInFanGe_p2 x E = wedgeInFanGe_p3 x E from rfl,
        ← wedgeInFanGe_eq_wedgeInFanGe_p3 hfanL hxd]
      exact hwedge
  have hk := HKIRPEP hcv2 hlun
  obtain ⟨-, -, -, -, hi, hj⟩ := hk
  obtain ⟨i, hiV, hi0, hi1, hiw, hiarc⟩ := hi
  obtain ⟨j, hjV, hj0, hj1, hjv, hjarc⟩ := hj
  exact ⟨i, j, by omega, by omega, hiV, hjV, hiw, hjv, hiarc, hjarc⟩

/-- **lunar v-半周槽位**：v-轨道（≤ m 步）落在平面 `{0, v, ρv}` 中且垂直轴
`cross3 v (ρv)`。端点：`k=0` 即 `v`；`k=m` 即 `w`（经 `Lunar` 共线
`w = c • v`）；内点：弧描述 `affGt {0,v}{ρv} ∩ V` 经 `AFF_GT_SUB_AFF_UNION`
落平面，正交由 `p10w_affine_perp` 供给。 -/
theorem LUNAR_VHALF_SLOTS {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hed : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hlun : Lunar v w V E) :
    ∃ m : ℕ, 0 < m ∧ m < V.ncard ∧ w = (rhoNode1 FF)^[m] v ∧
      (∀ k : ℕ, k ≤ m →
        (rhoNode1 FF)^[k] v ∈ affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3)) ∧
      (∀ k : ℕ, k ≤ m →
        (cross3 v (rhoNode1 FF v)) ⬝ᵥ ((rhoNode1 FF)^[k] v) = 0) := by
  obtain ⟨m, n, hm0, hn0, hmV, hnV, hwv, hvw, harc, -⟩ :=
    p10w_lunar_data hcl hed hlun
  have hvV : v ∈ V := hlun.2.1 (Set.mem_insert v ({w} : Set V3))
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hed
  have hvne : v ≠ 0 := fun hz =>
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hvV (by rw [hz]; exact collinear3_of_eq rfl)
  -- Lunar collinearity: w = c • v
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := v) (w1 := w) hvne).mp hlun.2.2.2
  have hcw : w = c • v := by
    have hc' := hc
    rw [sub_zero, sub_zero] at hc'
    exact hc'
  -- the plane membership at every orbit index k ≤ m
  have hpl : ∀ k : ℕ, k ≤ m →
      (rhoNode1 FF)^[k] v ∈ affineSpan ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, Function.iterate_zero_apply]
      exact subset_affineSpan ℝ _ (by simp)
    · rcases Nat.lt_or_ge k m with hlt | hge
      · -- interior: the arc equation + affGt ⊆ affineSpan
        have hmem : (rhoNode1 FF)^[k] v ∈ (affGt ({0, v} : Set V3)
            ({rhoNode1 FF v} : Set V3) ∩ V) := by
          rw [← harc]
          exact ⟨k, ⟨hkpos, hlt⟩, rfl⟩
        have hunion : (({0, v} : Set V3) ∪ ({rhoNode1 FF v} : Set V3))
            = ({(0:V3), v, rhoNode1 FF v} : Set V3) := by
          ext z
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        have hres := AFF_GT_SUB_AFF_UNION ({0, v} : Set V3) ({rhoNode1 FF v} : Set V3) hmem.1
        rwa [hunion] at hres
      · -- endpoint k = m: w fills the plane through the Lunar line
        have hkm : k = m := by omega
        rw [hkm, ← hwv, hcw]
        exact affineSpan_mono ℝ
          (by
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact Set.mem_insert _ _
            · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))
          (p9w_smul_mem_affineSpan_zero v c)
  refine ⟨m, hm0, hmV, hwv, hpl, fun k hk => ?_⟩
  exact p10w_affine_perp (a := v) (b := rhoNode1 FF v) (hpl k hk)

end W10bKit


/-! ### W10c lunar close-out (`p10w_*` continued; WSEWPCH wave W10c)

The **w-half** slots of `FAN_PERIMETER_LE_2PI_OF_LUNAR_STRUCT` and the fully
closed lunar branch.  The ιv-plane obstruction recorded in W10b collapses on
a real tree lemma: `AFF_IVS_RHO_NODE_EQQ` (LA5:8592) gives the cone identity
`affGt {0,w}{ρw} = affGt {0,v}{ιv}` (via
`LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT100` + `AFF_GT_SAME_WITH_ENDS` +
`COLL_IN_AFF_GT_AFF_GT_EQ`), so the w-arc interior (HKIRPEP:
`affGt {0,v}{ιv} ∩ V`) is literally the cone of the w-dart, hence lies in
`affineSpan {0,w,ρw}` by `AFF_GT_SUB_AFF_UNION`.  No AFFSIGN-mono machinery
needed. -/

section W10cKit

/-- **lunar w-半周槽位**：w-轨道（≤ n 步）落在平面 `{0, w, ρw}` 中且垂直轴
`cross3 w (ρw)`。关键改写：w-弧 = `affGt {0,v}{ιv} ∩ V`
`= affGt {0,w}{ρw} ∩ V`（`AFF_IVS_RHO_NODE_EQQ`，LA5 真证）。 -/
theorem LUNAR_WHALF_SLOTS {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hed : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hlun : Lunar v w V E) :
    ∃ n : ℕ, 0 < n ∧ n < V.ncard ∧ v = (rhoNode1 FF)^[n] w ∧
      (∀ k : ℕ, k ≤ n →
        (rhoNode1 FF)^[k] w ∈ affineSpan ℝ ({(0:V3), w, rhoNode1 FF w} : Set V3)) ∧
      (∀ k : ℕ, k ≤ n →
        (cross3 w (rhoNode1 FF w)) ⬝ᵥ ((rhoNode1 FF)^[k] w) = 0) := by
  obtain ⟨m, n, hm0, hn0, hmV, hnV, hwv, hvw, -, harc2⟩ :=
    p10w_lunar_data hcl hed hlun
  -- p2-world convex fan + cone identity
  obtain ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩ := hcl.1
  have hcl' : LocalFan V E FF := ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl' hed
  have hFFsub : FF ⊆ dart1OfFan V E := by
    rw [hFF0]
    exact (orbitMap_subset_of_permutesOn (hypermapOfFan 0 V E hfanL).faceMap_permutes hxd0).trans
      (p7w2_coe_darts hfanL).subset
  have hcv2 : convexLocalFan_p2 V E FF := by
    refine ⟨h2, fun x hx => ?_⟩
    obtain ⟨haz, hwedge⟩ := hcl.2 x hx
    have hxd : x ∈ dart1OfFan V E := hFFsub hx
    refine ⟨?_, ?_⟩
    · rw [show azimInFan_p2 x E = azimInFan_p3 x E from rfl,
        ← azimInFan_eq_azimInFan_p3 hfanL hxd]
      exact haz
    · rw [show wedgeInFanGe_p2 x E = wedgeInFanGe_p3 x E from rfl,
        ← wedgeInFanGe_eq_wedgeInFanGe_p3 hfanL hxd]
      exact hwedge
  have hcone : affGt ({0, v} : Set V3) ({ivsRhoNode1 FF v} : Set V3)
      = affGt ({0, w} : Set V3) ({rhoNode1 FF w} : Set V3) :=
    (AFF_IVS_RHO_NODE_EQQ hcv2 hlun).symm
  have hwV : w ∈ V := hlun.2.1 (Set.mem_insert_of_mem v (Set.mem_singleton w))
  have hvV : v ∈ V := hlun.2.1 (Set.mem_insert v ({w} : Set V3))
  have hwne : w ≠ 0 := fun hz =>
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hwV (by rw [hz]; exact collinear3_of_eq rfl)
  have hvne : v ≠ 0 := fun hz =>
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hvV (by rw [hz]; exact collinear3_of_eq rfl)
  -- Lunar collinearity: w = c • v (v ≠ 0), hence v = c⁻¹ • w
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := v) (w1 := w) hvne).mp hlun.2.2.2
  have hcw : w = c • v := by
    have hc' := hc
    rw [sub_zero, sub_zero] at hc'
    exact hc'
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hcw
    exact hwne hcw
  have hcv : v = c⁻¹ • w := by
    rw [hcw, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  have hpl : ∀ k : ℕ, k ≤ n →
      (rhoNode1 FF)^[k] w ∈ affineSpan ℝ ({(0:V3), w, rhoNode1 FF w} : Set V3) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, Function.iterate_zero_apply]
      exact subset_affineSpan ℝ _ (by simp)
    · rcases Nat.lt_or_ge k n with hlt | hge
      · -- interior: the w-arc cone IS the w-dart cone (AFF_IVS_RHO_NODE_EQQ)
        have hmem : (rhoNode1 FF)^[k] w ∈ (affGt ({0, v} : Set V3)
            ({ivsRhoNode1 FF v} : Set V3) ∩ V) := by
          rw [← harc2]
          exact ⟨k, ⟨hkpos, hlt⟩, rfl⟩
        rw [hcone] at hmem
        have hunion : (({0, w} : Set V3) ∪ ({rhoNode1 FF w} : Set V3))
            = ({(0:V3), w, rhoNode1 FF w} : Set V3) := by
          ext z
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        have hres := AFF_GT_SUB_AFF_UNION ({0, w} : Set V3) ({rhoNode1 FF w} : Set V3)
          hmem.1
        rwa [hunion] at hres
      · -- endpoint k = n: v fills the plane through the Lunar line
        have hkn : k = n := by omega
        rw [hkn, ← hvw, hcv]
        exact affineSpan_mono ℝ
          (by
            intro z hz
            rcases Set.mem_insert_iff.mp hz with rfl | hz2
            · exact Set.mem_insert _ _
            · rw [Set.mem_singleton_iff] at hz2
              subst hz2
              exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))
          (p9w_smul_mem_affineSpan_zero w c⁻¹)
  refine ⟨n, hn0, hnV, hvw, hpl, fun k hk => ?_⟩
  exact p10w_affine_perp (a := w) (b := rhoNode1 FF w) (hpl k hk)

end W10cKit

/-- **WSEWPCH lunar 支全闭**（polar_fan.hl:2360-2537 的组装）：凸局部扇 + lunar
二元组（`Lunar v w V E`）⟹ 周长 ≤ 2π。组装 = `p10w_lunar_data`（m/n/端点）
+ `LUNAR_VHALF_SLOTS` / `LUNAR_WHALF_SLOTS`（双半槽位，任一方向经
`w6a orbit dis` 对齐）+ `FAN_PERIMETER_LE_2PI_OF_LUNAR_STRUCT`（W10a 望远镜）。 -/
theorem FAN_PERIMETER_LE_2PI_OF_LUNAR {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (hcl : ConvexLocalFan V E FF)
    (hed : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hlun : Lunar v w V E) :
    fanPerimeter V E FF ≤ 2 * Real.pi := by
  obtain ⟨m, n, hm0, hn0, hmV, hnV, hwv, hvw, -, -⟩ := p10w_lunar_data hcl hed hlun
  obtain ⟨m', hm0', hmV', hwv', hpl2, hperp2⟩ := LUNAR_VHALF_SLOTS hcl hed hlun
  obtain ⟨n', hn0', hnV', hvw', hpl1, hperp1⟩ := LUNAR_WHALF_SLOTS hcl hed hlun
  have hvV : v ∈ V := hlun.2.1 (Set.mem_insert v ({w} : Set V3))
  have hwV : w ∈ V := hlun.2.1 (Set.mem_insert_of_mem v (Set.mem_singleton w))
  have hcol : Collinear ℝ ({(0:V3), v, w} : Set V3) := hlun.2.2.2
  -- witness alignment (both directions inherit uniqueness from the rho cycle)
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hed
  have hmm : m = m' := by
    by_contra hne
    have heq : (rhoNode1 FF)^[m'] v = (rhoNode1 FF)^[m] v := by
      rw [← hwv', ← hwv]
    have heqP : (rhoNode1_p2 FF)^[m'] v = (rhoNode1_p2 FF)^[m] v := heq
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (rhoNode1_p2 FF)^[m'] v ≠ (rhoNode1_p2 FF)^[m] v :=
        LOFA_IMP_DIS_ELMS2 h2 hvV m m' hlt (by
          rw [LOFA_IMP_CARD_FF_V_EQ h2]
          exact hmV')
      exact h1 heqP
    · have h1 : (rhoNode1_p2 FF)^[m] v ≠ (rhoNode1_p2 FF)^[m'] v :=
        LOFA_IMP_DIS_ELMS2 h2 hvV m' m hgt (by
          rw [LOFA_IMP_CARD_FF_V_EQ h2]
          exact hmV)
      exact h1 heqP.symm
  have hnn : n = n' := by
    by_contra hne
    have heq : (rhoNode1 FF)^[n'] w = (rhoNode1 FF)^[n] w := by
      rw [← hvw', ← hvw]
    have heqP : (rhoNode1_p2 FF)^[n'] w = (rhoNode1_p2 FF)^[n] w := heq
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (rhoNode1_p2 FF)^[n'] w ≠ (rhoNode1_p2 FF)^[n] w :=
        LOFA_IMP_DIS_ELMS2 h2 hwV n n' hlt (by
          rw [LOFA_IMP_CARD_FF_V_EQ h2]
          exact hnV')
      exact h1 heqP
    · have h1 : (rhoNode1_p2 FF)^[n] w ≠ (rhoNode1_p2 FF)^[n'] w :=
        LOFA_IMP_DIS_ELMS2 h2 hwV n' n hgt (by
          rw [LOFA_IMP_CARD_FF_V_EQ h2]
          exact hnV)
      exact h1 heqP.symm
  subst hmm
  subst hnn
  exact FAN_PERIMETER_LE_2PI_OF_LUNAR_STRUCT hcl hed hvV hwV hcol m n hn0 hm0
    hmV hnV hvw hwv hperp1 hperp2 hpl1 hpl2


/-! ### W11a BGMIFTE prologue (`p11w_*`; WSEWPCH wave W11a)

Self-contained pieces of HOL `BGMIFTE` (polar_fan.hl:1065) that do not need
the aff_ge/affsign assembly of conclusion 1:

* `P11W_PRIME_NE_ZERO` — the polar map `p v = v × ρv` is nowhere zero on `V`
  (HOL BGMIFTE prologue: `!v. v IN V ==> ~(prime' v = vec 0)`).
* `P11W_ARC_HALF` — **BGMIFTE conclusion 4's first arc half**: for every
  `v ∈ V`, `arcV 0 (p v) (p (ρv)) = π - interiorAngle1 0 FF (ρv)` with both
  bounds.  Instantiation of the real W5b engine `p7w2_half_polar_arc`
  (IVS_RHO_IDD + CHARACTER_OF_RHO_NODE2 + INTERIOR_ANGLE1_POS + the BGMIFTE
  premise `hia`).
* `p11w_card_of_inj` — `V'.ncard = V.ncard` from injectivity of the polar map
  (BGMIFTE conclusion 3's last step; injectivity itself is W11b). -/

section W11aKit

/-- BGMIFTE 前奏：极映射 `p v = v × ρv` 在 `V` 上非零。 -/
theorem P11W_PRIME_NE_ZERO {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) : ∀ v ∈ V, cross3 v (rhoNode1 FF v) ≠ 0 := by
  intro v hv
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1
    (LOCAL_FAN_IMP_HEDGE hcl.1)
  have hnc : ¬ Collinear ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv
  intro hz
  refine hnc (COLLINEAR_CROSS_0.mpr ?_)
  have hcoe : (WithLp.toLp 2 (crossProduct ((v - 0 : V3) : Fin 3 → ℝ)
      ((rhoNode1 FF v - 0 : V3) : Fin 3 → ℝ)) : V3) = cross3 v (rhoNode1 FF v) := by
    refine p7w_v3_eq ?_
    rw [coe_toLp, coe_subP, coe_subP, coe_zeroV, sub_zero, sub_zero, coe_cross3P]
  rw [hcoe, hz]

/-- **BGMIFTE 结论 4 第一弧半**（polar_fan.hl:1065 第四合取的第一 ∀）：
`arcV 0 (p v) (p (ρv)) = π - interiorAngle1 0 FF (ρv)`，且两条界。 -/
theorem P11W_ARC_HALF {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    ∀ v ∈ V,
      arcV (0 : V3) (cross3 v (rhoNode1 FF v))
            (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)))
          = Real.pi - interiorAngle1 (0 : V3) FF (rhoNode1 FF v) ∧
        0 < arcV (0 : V3) (cross3 v (rhoNode1 FF v))
              (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))) ∧
        arcV (0 : V3) (cross3 v (rhoNode1 FF v))
              (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))) < Real.pi := by
  intro v hv
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
  have hrmem : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
  have h4 : ¬ Collinear ℝ (({0, rhoNode1 FF v,
      rhoNode1 (FF) (rhoNode1 FF v)} : Set V3)) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hrmem
  have h5 : ¬ Collinear ℝ (({0, v, rhoNode1 FF v} : Set V3)) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv
  have h3 : ivsRhoNode1 FF (rhoNode1 FF v) = v := IVS_RHO_IDD h2 hv
  exact p7w2_half_polar_arc (V := V) (FF := FF) (v := v) (a := rhoNode1 FF v)
    (b := rhoNode1 FF (rhoNode1 FF v)) rfl rfl h3 h4 h5
    (hia _ hrmem) (INTERIOR_ANGLE1_POS h2 hrmem)

/-- BGMIFTE 结论 3 收尾步：极映射在 `V` 上单射 ⟹ `V'.ncard = V.ncard`
（`V' = image p V`，即 `polarFan` 的第一分量）。 -/
theorem p11w_card_of_inj {V : Set V3} {p : V3 → V3}
    (hinj : ∀ v ∈ V, ∀ w ∈ V, p v = p w → v = w) :
    (image p V).ncard = V.ncard := by
  have hInj : Set.InjOn p V := fun a ha b hb hab => hinj a ha b hb hab
  rw [Set.InjOn.ncard_image hInj]

end W11aKit


/-! ### W11b1 BGMIFTE conclusion-1 prologue (`p11w_*`; WSEWPCH wave W11b1)

* `P11W_AFFSIGN_SUBSET_AFFINESPAN` — the **reconstructed** sign-transport
  lemma (NOT a port: `AFFSIGN_MONO_SHUFFLE`/`AFF_GE_EQ_AFFINE_HULL` have no
  definition anywhere in `reference/flyspeck/` — only polar_fan.hl:1449
  references them).  The mathematical content consumed there is
  `Affsign sgn s t v ⟹ v ∈ affineSpan (s ∪ t)`, proved here from the
  `Affsign` semantics (PackingAuto18 carries a private twin at :7437 which is
  not importable from LA7; this is a fresh proof of the same statement).
* `P11W_PRIME_NCOL` / `P11W_PRIME_INJ` / `P11W_CARD` — the HOL BGMIFTE
  opening block (polar_fan.hl:1146-1180): the polar map's non-collinearity
  (cross-algebra `lemma2/lemma3` machinery), injectivity on `V`, and
  **BGMIFTE conclusion 3** (`V'.ncard = V.ncard`). -/

section W11b1Kit

/-- `Affsign` → `affineSpan` 桥（**新建件**，非移植：HOL
`AFFSIGN_MONO_SHUFFLE` 在 reference 全树无定义、仅 polar_fan.hl:1449 消费；
其在那里承担的实际数学内容即本件。证法：取 `w₀ ∈ s ∪ t`，差分落入
`vectorSpan (s ∪ t)`，再沿仿射方向平移回去。） -/
theorem P11W_AFFSIGN_SUBSET_AFFINESPAN {sgn : ℝ → Prop} {s t : Set V3} {v : V3}
    (hv : Affsign sgn s t v) : v ∈ (affineSpan ℝ (s ∪ t) : Set V3) := by
  obtain ⟨f, hfin, hvec, -, hone⟩ := hv
  by_cases hF : hfin.toFinset = ∅
  · rw [hF, Finset.sum_empty] at hone
    norm_num at hone
  · obtain ⟨w₀, hw₀F⟩ := Finset.nonempty_iff_ne_empty.2 hF
    have hw₀S : w₀ ∈ (s ∪ t : Set V3) := (Set.Finite.mem_toFinset hfin).1 hw₀F
    have key : v - w₀ = ∑ w ∈ hfin.toFinset, f w • (w - w₀) := by
      have h1 : (∑ w ∈ hfin.toFinset, f w • (w - w₀) : V3)
          = (∑ w ∈ hfin.toFinset, f w • w) - (∑ w ∈ hfin.toFinset, f w) • w₀ := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ => by rw [smul_sub]
      rw [h1, hvec, hone, one_smul]
    have hd : (v - w₀ : V3) ∈ vectorSpan ℝ (s ∪ t : Set V3) := by
      rw [vectorSpan_def, key]
      refine Submodule.sum_mem _ fun w hw => ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_vsub.2
        ⟨w, (Set.Finite.mem_toFinset hfin).1 hw, w₀, hw₀S, rfl⟩))
    have hvv : v = (v -ᵥ w₀) +ᵥ w₀ := by rw [vsub_vadd]
    rw [SetLike.mem_coe, hvv,
      AffineSubspace.vadd_mem_iff_mem_direction (v -ᵥ w₀)
        (subset_affineSpan ℝ (s ∪ t : Set V3) hw₀S),
      direction_affineSpan]
    exact hd

/-- 非平行向量的纯量等式杀手（HOL BGMIFTE lemma3 的按需形）：
`α • x = β • y`，`x, y ≠ 0` 且 `{0,x,y}` 不共线 ⟹ 两个系数全零。 -/
private theorem p11w_smul_eq_zero {x y : V3} (hx : x ≠ 0) (hy : y ≠ 0)
    (hncol : ¬ Collinear ℝ ({(0:V3), x, y} : Set V3)) {α β : ℝ}
    (h : α • x = β • y) : α = 0 ∧ β = 0 := by
  constructor
  · by_contra hα
    apply hncol
    have hxey : x = (α⁻¹ * β) • y := by
      calc x = α⁻¹ • (α • x) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
        _ = α⁻¹ • (β • y) := by rw [h]
        _ = (α⁻¹ * β) • y := by rw [smul_smul]
    have hcol : Collinear ℝ ({(0:V3), y, x} : Set V3) :=
      (collinear3_iff_smul (v := (0:V3)) (w := y) (w1 := x) hy).mpr
        ⟨α⁻¹ * β, by rw [hxey, sub_zero, sub_zero]⟩
    rwa [show ({(0:V3), y, x} : Set V3) = ({(0:V3), x, y} : Set V3) from by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto] at hcol
  · by_contra hβ
    apply hncol
    have hyex : y = (β⁻¹ * α) • x := by
      calc y = β⁻¹ • (β • y) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        _ = β⁻¹ • (α • x) := by rw [← h]
        _ = (β⁻¹ * α) • x := by rw [smul_smul]
    have hcol : Collinear ℝ ({(0:V3), x, y} : Set V3) :=
      (collinear3_iff_smul (v := (0:V3)) (w := x) (w1 := y) hx).mpr
        ⟨β⁻¹ * α, by rw [hyex, sub_zero, sub_zero]⟩
    exact hcol

/-- **BGMIFTE 前奏：极映射两两非共线**（HOL polar_fan.hl:1146-1170）：
`v ≠ w` 时 `{0, v×ρv, w×ρw}` 不共线。交叉代数：共线 ⟹ 双叉积为零 ⟹
展开 `(v×ρv)×(w×ρw) = α•ρv - β•v` ⟹ 非平行系数全零
（`p11w_smul_eq_zero`）⟹ `α = 0` 与 `GENERIC_LOCAL_FAN_AZIM_POS` 的 sin
正性矛盾（`SIN_AZIM_MUTUAL_CROSS`；`v = ρw` 边界改用 β 与对称方向 +
SEMI_IDE 收口）。 -/
theorem P11W_PRIME_NCOL {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    ∀ v ∈ V, ∀ w ∈ V, v ≠ w →
      ¬ Collinear ℝ ({(0:V3), cross3 v (rhoNode1 FF v),
        cross3 w (rhoNode1 FF w)} : Set V3) := by
  intro v hv w hw hne hcol
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
  have hrmemv : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
  have hncv : ¬ Collinear ℝ ({(0:V3), v, rhoNode1 FF v} : Set V3) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv
  have hvne : v ≠ 0 := fun hz =>
    hncv (by rw [hz]; exact collinear3_of_eq rfl)
  have hrvne : rhoNode1 FF v ≠ 0 := fun hz =>
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hrmemv (by rw [hz]; exact collinear3_of_eq rfl)
  have hncv' : ¬ Collinear ℝ ({(0:V3), rhoNode1 FF v, v} : Set V3) := by
    rw [show ({(0:V3), rhoNode1 FF v, v} : Set V3)
        = ({(0:V3), v, rhoNode1 FF v} : Set V3) from by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto]
    exact hncv
  -- 交叉零：collinear ⟹ pv × pw = 0
  have hcross0 : cross3 (cross3 v (rhoNode1 FF v)) (cross3 w (rhoNode1 FF w)) = 0 := by
    have h := (COLLINEAR_CROSS_0 (x := (0:V3)) (y := cross3 v (rhoNode1 FF v))
      (z := cross3 w (rhoNode1 FF w))).mp hcol
    have hcoe : (WithLp.toLp 2 (crossProduct
        ((cross3 v (rhoNode1 FF v) - 0 : V3) : Fin 3 → ℝ)
        ((cross3 w (rhoNode1 FF w) - 0 : V3) : Fin 3 → ℝ)) : V3)
        = cross3 (cross3 v (rhoNode1 FF v)) (cross3 w (rhoNode1 FF w)) := by
      refine p7w_v3_eq ?_
      rw [coe_toLp, coe_subP, coe_subP, coe_zeroV, sub_zero, sub_zero]
      simp only [coe_cross3P]
    rwa [hcoe] at h
  -- 展开：(v×ρv)×(w×ρw) = α•ρv - β•v
  have hexp : cross3 (cross3 v (rhoNode1 FF v)) (cross3 w (rhoNode1 FF w))
      = ((cross3 w (rhoNode1 FF w)) ⬝ᵥ v) • rhoNode1 FF v
        - (rhoNode1 FF v ⬝ᵥ (cross3 w (rhoNode1 FF w))) • v := by
    refine p7w_v3_eq ?_
    rw [coe_cross3P, coe_cross3P, coe_subP, coe_smulP, coe_smulP]
    rw [cross_cross_eq_smul_sub_smul]
    congr 1
    rw [dotProduct_comm]
  have hsmul : ((cross3 w (rhoNode1 FF w)) ⬝ᵥ v) • rhoNode1 FF v
      = (rhoNode1 FF v ⬝ᵥ (cross3 w (rhoNode1 FF w))) • v := by
    have h := hcross0
    rw [hexp] at h
    exact sub_eq_zero.mp h
  have hαβ := p11w_smul_eq_zero hrvne hvne hncv' hsmul
  by_cases hvr : v = rhoNode1 FF w
  · -- 边界情形 v = ρw：α 自动为零；改用 β 与对称方向
    have hβ0 : rhoNode1 FF v ⬝ᵥ (cross3 w (rhoNode1 FF w)) = 0 := hαβ.2
    have h1 : rhoNode1 FF v ⬝ᵥ (cross3 w (rhoNode1 FF w))
        = (cross3 v (rhoNode1 FF v)) ⬝ᵥ w := by
      rw [hvr]
      rw [p7w_dot_coe, p7w_dot_coe, coe_cross3P, coe_cross3P]
      rw [triple_product_permutation]
      exact dotProduct_comm _ _
    have hβ' : (cross3 v (rhoNode1 FF v)) ⬝ᵥ w = 0 := by
      rw [← h1]
      exact hβ0
    have hwrv : w ≠ rhoNode1 FF v := by
      intro hcon
      have hsem : rhoNode1 FF (rhoNode1 FF w) ≠ w := LOCAL_FAN_IMP_NOT_SEMI_IDE h2 hw
      apply hsem
      rw [← hvr, hcon]
    have hsin := GENERIC_LOCAL_FAN_AZIM_POS hcl hedge hg hia v w hv hw
      (fun hwv => hne hwv.symm) hwrv
    have hpos' : (0:ℝ) < (cross3 v (rhoNode1 FF v)) ⬝ᵥ w :=
      (SIN_AZIM_MUTUAL_CROSS v (rhoNode1 FF v) w).2.1.mp hsin
    rw [hβ'] at hpos'
    exact lt_irrefl _ hpos'
  · -- 主情形：α = 0 与 GENERIC_POS (w, v) 的 sin 正性矛盾
    have hsin := GENERIC_LOCAL_FAN_AZIM_POS hcl hedge hg hia w v hw hv hne hvr
    have hpos' : (0:ℝ) < (cross3 w (rhoNode1 FF w)) ⬝ᵥ v :=
      (SIN_AZIM_MUTUAL_CROSS w (rhoNode1 FF w) v).2.1.mp hsin
    have h0 : (cross3 w (rhoNode1 FF w)) ⬝ᵥ v = 0 := hαβ.1
    rw [h0] at hpos'
    exact lt_irrefl _ hpos'

/-- **BGMIFTE 前奏：极映射在 `V` 上单射**（HOL polar_fan.hl:1171-1180）。 -/
theorem P11W_PRIME_INJ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    ∀ v ∈ V, ∀ w ∈ V, cross3 v (rhoNode1 FF v) = cross3 w (rhoNode1 FF w) → v = w := by
  intro v hv w hw heq
  by_contra hne
  refine P11W_PRIME_NCOL hcl hedge hg hia v hv w hw hne ?_
  rw [heq]
  exact collinear3_pair_right rfl

/-- **BGMIFTE 结论 3**：极扇顶点数不变（`V' = (polarFan V E FF).1`）。 -/
theorem P11W_CARD {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    (polarFan V E FF).1.ncard = V.ncard := by
  have hinj := P11W_PRIME_INJ hcl hedge hg hia
  simp only [polarFan]
  exact p11w_card_of_inj hinj

end W11b1Kit

/-! ### W11b2a polar-fan FAN basics (`p11w_*`; WSEWPCH wave W11b2a)

HOL polar_fan.hl:1217-1260 entry block of BGMIFTE conclusion 1: four of the
six FAN conjuncts on the polar pair `(V', E') = ((polarFan V E FF).1, .2.1)`.
Consumes the W11b1 pieces (`P11W_PRIME_INJ` / `P11W_PRIME_NCOL` /
`P11W_PRIME_NE_ZERO`) plus `LOCAL_FAN_IN_FF_DISTINCT` / PRIME injectivity.

Remaining FAN conjuncts (fan7's aff_ge separation) and the local_fan/dih2k
assembly + wedge conditions are W11b2a2/b2b (see lane DELIVERY). -/

section W11b2aKit

/-- 极扇边集是图（每条边恰两点）：`{p v, p (ρv)}` 两端由 `P11W_PRIME_INJ` +
`ρv ≠ v`（`LOCAL_FAN_IN_FF_DISTINCT`）互异。 -/
theorem P11W_POLAR_GRAPH {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    Graph ((polarFan V E FF).2.1) := by
  intro e he
  simp only [polarFan, Set.mem_image] at he
  obtain ⟨v, hv, rfl⟩ := he
  have hinj := P11W_PRIME_INJ hcl hedge hg hia
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
  have hrmem : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
  have hdart : (v, rhoNode1 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h2).1 v hv
  have hvv : v ≠ rhoNode1 FF v := LOCAL_FAN_IN_FF_DISTINCT h2 hdart
  have hne : cross3 v (rhoNode1 FF v)
      ≠ cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)) := by
    intro heq
    exact hvv (hinj v hv (rhoNode1 FF v) hrmem heq)
  refine ⟨(Set.finite_singleton _).insert _, ?_⟩
  have htf : ((Set.finite_singleton
      (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)))).insert
        (cross3 v (rhoNode1 FF v))).toFinset
      = ({cross3 v (rhoNode1 FF v),
          cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [htf, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- 极扇的 FAN 基本条件（4/6）：Graph、fan1（有限非空）、fan2（0 不在顶点集）、
fan6（边不过 0 共线）。HOL polar_fan.hl:1217-1260 入口段。 -/
theorem P11W_POLAR_FAN_BASIC {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    Graph ((polarFan V E FF).2.1) ∧
      fan1 (0:V3) ((polarFan V E FF).1) ((polarFan V E FF).2.1) ∧
      fan2 (0:V3) ((polarFan V E FF).1) ((polarFan V E FF).2.1) ∧
      fan6 (0:V3) ((polarFan V E FF).1) ((polarFan V E FF).2.1) := by
  obtain ⟨hfanL, x0, hxd0, hFF0, hD, hee⟩ := hcl.1
  have hVfin : V.Finite := hfanL.2.2.1.1
  have hVne : V ≠ ∅ := hfanL.2.2.1.2
  refine ⟨P11W_POLAR_GRAPH hcl hedge hg hia, ?_, ?_, ?_⟩
  · -- fan1: 像的有限非空
    simp only [polarFan, fan1]
    constructor
    · exact hVfin.image _
    · intro hz
      rw [Set.image_eq_empty] at hz
      exact hVne hz
  · -- fan2: 极映射非零
    simp only [polarFan, fan2]
    intro h0
    obtain ⟨v, hv, hvp⟩ := h0
    exact P11W_PRIME_NE_ZERO hcl v hv hvp
  · -- fan6: 边 {p v, p(ρv)} 与 0 不共线（= P11W_PRIME_NCOL at (v, ρv)）
    intro e he
    simp only [polarFan, Set.mem_image] at he
    obtain ⟨v, hv, rfl⟩ := he
    have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
    have hdart : (v, rhoNode1 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h2).1 v hv
    have hvv : v ≠ rhoNode1 FF v := LOCAL_FAN_IN_FF_DISTINCT h2 hdart
    have hrmem : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
    have hnc := P11W_PRIME_NCOL hcl hedge hg hia v hv (rhoNode1 FF v) hrmem hvv
    simpa using hnc

end W11b2aKit


/-! ### W11b2 polar dart-layer identities (`p11w2_*`; WSEWPCH wave W11b2)

First file of the BGMIFTE conclusion-1 assembly (HOL `polar_fan.hl`
1704-1740): the polar fan's ordered-pair / dart / edge-neighbour sets in the
`_p3` HYP vocabulary consumed by `localFan_p3` (bridged back to LA1's
`LocalFan` by `localFanEquiv_p35`).  All four identities are set algebra over
the image presentation `E' = {p v, p (ρ v)}`, made injective by
`P11W_PRIME_INJ` (W11b1).

Survey note (W11b2 erratum): `FAN 0 V' E'` itself is **not** yet in the tree
— the polar fan7 instantiation (`hvs`/`hve`/`hee`, HOL 1400-1698) is still a
missing prerequisite, so `localFan_p3 V' E' FF'` (HOL 1698-1978) remains
blocked on it.  `p11w2_polar_hvs` below is the first of those three
conditions. -/

section W11b2Kit

/-- 极扇顶点集 `V'`（`polarFan` 第一分量，逐字）。 -/
noncomputable def polarV (V : Set V3) (FF : Set (V3 × V3)) : Set V3 :=
  image (fun v : V3 => cross3 v (rhoNode1 FF v)) V

/-- 极扇边集 `E'`（`polarFan` 第二分量，逐字）。 -/
noncomputable def polarE (V : Set V3) (FF : Set (V3 × V3)) : Set (Set V3) :=
  image (fun v : V3 => ({cross3 v (rhoNode1 FF v),
    cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))} : Set V3)) V

/-- 极扇 dart 集 `FF'`（`polarFan` 第三分量，逐字）。 -/
noncomputable def polarFF (V : Set V3) (FF : Set (V3 × V3)) : Set (V3 × V3) :=
  image (fun v : V3 => (cross3 v (rhoNode1 FF v),
    cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)))) V

/-- 反向 dart 集（HOL `FF''`）。 -/
noncomputable def polarFFrev (V : Set V3) (FF : Set (V3 × V3)) : Set (V3 × V3) :=
  image (fun v : V3 => (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)),
    cross3 v (rhoNode1 FF v))) V

/-- `polarFan` 的三分量就是上面的逐字呈现（`let` 消去后 `rfl`）。 -/
theorem p11w2_polarFan_components (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) :
    polarFan V E FF = (polarV V FF, polarE V FF, polarFF V FF) := rfl

/-- `ord_pairs` 层（HOL `darts_of_hyp` 的首件）：`FF' ∪ FF''`。 -/
theorem p11w2_polar_ordPairs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_hcl : ConvexLocalFan V E FF) (_hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (_hg : Generic V E)
    (_hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    ordPairs_p3 (polarE V FF) = polarFF V FF ∪ polarFFrev V FF := by
  ext d
  constructor
  · intro hd
    obtain ⟨v, hv, hveq⟩ := hd
    rcases Set.pair_eq_pair_iff.mp hveq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨v, hv, Prod.ext h1 h2⟩
    · right
      exact ⟨v, hv, Prod.ext h2 h1⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨v, hv, Set.pair_comm _ _⟩

/-- 边邻集（HOL `polar_fan.hl:1714` 的 `EE (p v) E'`）：`{p(ρv), p(ιv)}`。 -/
theorem p11w2_polar_EE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) {v : V3} (hv : v ∈ V) :
    EE_p3 (cross3 v (rhoNode1 FF v)) (polarE V FF) =
      ({cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)),
        cross3 (ivsRhoNode1 FF v) (rhoNode1 FF (ivsRhoNode1 FF v))} : Set V3) := by
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
  ext w
  constructor
  · intro hw
    have hw' : ({cross3 v (rhoNode1 FF v), w} : Set V3) ∈ polarE V FF := hw
    obtain ⟨a, ha, hweq⟩ := hw'
    -- `hweq : {p a, p(ρa)} = {p v, w}`
    rcases Set.pair_eq_pair_iff.mp hweq with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · -- `p a = p v`, `p(ρa) = w`
      have hva : v = a := P11W_PRIME_INJ hcl hedge hg hia v hv a ha h1.symm
      refine Set.mem_insert_iff.mpr (Or.inl ?_)
      rw [← hva] at h2'
      exact h2'.symm
    · -- `p a = w`, `p(ρa) = p v`：`a = ι v`
      have hrv'aV : rhoNode1 FF a ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 ha
      have hva : v = rhoNode1 FF a :=
        P11W_PRIME_INJ hcl hedge hg hia v hv (rhoNode1 FF a) hrv'aV h2'.symm
      have hι : ivsRhoNode1 FF v = a := by
        rw [hva]
        exact w6a_ivs_idd h2 ha
      refine Set.mem_insert_iff.mpr (Or.inr ?_)
      rw [Set.mem_singleton_iff]
      rw [hι]
      exact h1.symm
  · intro hw
    have hw' : w ∈ ({cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)),
        cross3 (ivsRhoNode1 FF v) (rhoNode1 FF (ivsRhoNode1 FF v))} : Set V3) := hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    rcases hw' with hw' | hw'
    · have hgoal : ({cross3 v (rhoNode1 FF v), w} : Set V3) ∈ polarE V FF := by
        rw [hw']
        exact ⟨v, hv, rfl⟩
      exact hgoal
    · have hgoal : ({cross3 v (rhoNode1 FF v), w} : Set V3) ∈ polarE V FF := by
        rw [hw']
        refine ⟨ivsRhoNode1 FF v, IVS_RHO_NODE1_IN_V hcl.1 hedge v hv, ?_⟩
        simp only []
        rw [show rhoNode1 FF (ivsRhoNode1 FF v) = v from w6a_rho_ivs h2 hv]
        exact Set.pair_comm _ _
      exact hgoal

/-- `self_pairs` 为空：`V'` 上每个点都有边（`EE (p v) E' ∋ p(ρv)`）。 -/
theorem p11w2_polar_selfPairs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    selfPairs_p3 (polarE V FF) (polarV V FF) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨a1, a2⟩ ⟨-, haV, hEE⟩
  obtain ⟨v, hv, rfl⟩ := haV
  have hEE' := p11w2_polar_EE hcl hedge hg hia hv
  rw [hEE'] at hEE
  have hmem : cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)) ∈
      ({cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)),
        cross3 (ivsRhoNode1 FF v) (rhoNode1 FF (ivsRhoNode1 FF v))} : Set V3) := by
    rw [Set.mem_insert_iff]
    left
    rfl
  rw [hEE] at hmem
  simpa using hmem

/-- `darts_of_hyp` 层（HOL `polar_fan.hl:1704`）：`FF' ∪ FF''`。 -/
theorem p11w2_polar_darts {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    dartsOfHyp_p3 (polarE V FF) (polarV V FF) = polarFF V FF ∪ polarFFrev V FF := by
  rw [dartsOfHyp_p3, p11w2_polar_ordPairs hcl hedge hg hia,
    p11w2_polar_selfPairs hcl hedge hg hia, Set.union_empty]

/-- 极扇的 `hvs` 条件（`FAN_AFF_GT_CONDITION` 前题之一）：两条极射线的闭锥
之交只有基点（`P11W_PRIME_NCOL` + 射线系数形）。 -/
theorem p11w2_polar_hvs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    ∀ v ∈ polarV V FF, ∀ w ∈ polarV V FF,
      affGe ({(0:V3)} : Set V3) {v} ∩ affGe ({(0:V3)} : Set V3) {w}
        = affGe ({(0:V3)} : Set V3) ({v} ∩ {w}) := by
  intro v hv w hw
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, rfl⟩ := hw
  by_cases hab : a = b
  · subst hab
    rw [Set.inter_self, Set.inter_self]
  · have hpa0 : cross3 a (rhoNode1 FF a) ≠ 0 := P11W_PRIME_NE_ZERO hcl a ha
    have hpb0 : cross3 b (rhoNode1 FF b) ≠ 0 := P11W_PRIME_NE_ZERO hcl b hb
    have hpne : cross3 a (rhoNode1 FF a) ≠ cross3 b (rhoNode1 FF b) := by
      intro heq
      exact hab (P11W_PRIME_INJ hcl hedge hg hia a ha b hb heq)
    have hinter : ({cross3 a (rhoNode1 FF a)} : Set V3) ∩
        {cross3 b (rhoNode1 FF b)} = ∅ := p11w2_single_inter_single hpne
    rw [hinter, P11W_AFFGE_EMPTY]
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨s, hs, hys⟩ :=
        (P11W2_GE_SINGLE_REL (x := (0:V3))
          (v := cross3 a (rhoNode1 FF a)) (Ne.symm hpa0)).mp hy1
      obtain ⟨t, ht, hyt⟩ :=
        (P11W2_GE_SINGLE_REL (x := (0:V3))
          (v := cross3 b (rhoNode1 FF b)) (Ne.symm hpb0)).mp hy2
      rw [Set.mem_singleton_iff]
      by_cases hs0 : s = 0
      · rw [hs0, zero_smul] at hys
        simpa using hys
      · have ht0 : t ≠ 0 := by
          intro ht0'
          rw [ht0', zero_smul] at hyt
          have hsa : s • (cross3 a (rhoNode1 FF a) - 0) = 0 := by
            rw [← hys, hyt]
          have hpa' : cross3 a (rhoNode1 FF a) - 0 = 0 :=
            (smul_eq_zero.mp hsa).resolve_left hs0
          exact hpa0 (sub_eq_zero.mp hpa')
        have hEq : s • (cross3 a (rhoNode1 FF a) - 0)
            = t • (cross3 b (rhoNode1 FF b) - 0) := by
          rw [← hys, hyt]
        have hpb' : cross3 b (rhoNode1 FF b) - 0
            = (t⁻¹ * s) • (cross3 a (rhoNode1 FF a) - 0) := by
          have h' := congrArg (fun z => t⁻¹ • z) hEq
          rw [smul_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul] at h'
          exact h'.symm
        have hcol : Collinear3 0 (cross3 a (rhoNode1 FF a)) (cross3 b (rhoNode1 FF b)) :=
          (collinear3_iff_smul (v := (0:V3)) (w := cross3 a (rhoNode1 FF a))
            (w1 := cross3 b (rhoNode1 FF b)) hpa0).mpr ⟨t⁻¹ * s, hpb'⟩
        exact (P11W_PRIME_NCOL hcl hedge hg hia a ha b hb hab hcol).elim
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact
        ⟨(P11W2_GE_SINGLE_REL (x := (0:V3))
            (v := cross3 a (rhoNode1 FF a)) (Ne.symm hpa0)).mpr
            ⟨0, le_refl 0, by simp⟩,
          (P11W2_GE_SINGLE_REL (x := (0:V3))
            (v := cross3 b (rhoNode1 FF b)) (Ne.symm hpb0)).mpr
            ⟨0, le_refl 0, by simp⟩⟩

end W11b2Kit

/-! ### W11b2-ii polar fan7 前题（`p11w2_*`；WSEWPCH wave W11b2）

`hve`/`hee` 的极化验证 + `hsub` + `FAN 0 V' E'` 装配。与 W11b2-i 的 `hvs`
同一骨架（射线/锥的差向量系数形 + `P11W_PRIME_NCOL`），但换用**点积探针**
（每证一次 `y ⬝ᵥ ρx` 的两侧展开）代替 HOL 1400-1698 的楔形/azim 序论证：

* 关键正性事实 `p11w2_polar_pos_dot`：`GENERIC_LOCAL_FAN_AZIM_POS` +
  `SIN_AZIM_MUTUAL_CROSS` 给出 `0 < (p v) ⬝ᵥ w`（`w ∈ V`，`w ≠ v`，`w ≠ ρv`）；
* `p v ⊥ v`、`p v ⊥ ρ v`（叉积正交，`p11w2_cross3_dot_*`）；
* `ρ` 在 `V` 上单射（`w6a_rho_inj`）与 `ρ(ρv) ≠ v`（`LOCAL_FAN_IMP_NOT_SEMI_IDE`）
  处理相邻边的例外情形。

`hve` 的核心：若 `y ∈ Gt{0}{p a} ∩ Gt{0}{p b, p(ρb)}`，则点积 `ρb` 两侧给
`s·((p a)·ρb) = 0`（`s > 0`）——`ρb ∉ {a, ρa}` 时与正性冲突；`ρb = a`（即
`ρb ∈` 边的左端）与 `ρa = ρb`（`a = b`）两个例外由非共线 `P11W_PRIME_NCOL`
收口。`hee` 同构：探针 `ρa` 给出 `u·((p b)·ρa) + v·((p ρb)·ρa) = 0`，例外情形
`ρa = b` / `ρa = ρ b` / `ρa = ρ(ρb)` 用换探针（`ρ(ρa)` 或消去一项）归约。 -/

section W11b2Kit2

/-- `cross3 a a = 0`。 -/
private theorem p11w2_cross3_self (a : V3) : cross3 a a = 0 := by
  have h := p7w_cross3_smul_right_self a 1
  simpa using h

/-- `(a × b) ⬝ᵥ b = 0`（叉积与其第二因子正交）。 -/
private theorem p11w2_cross3_dot_right (a b : V3) : (cross3 a b) ⬝ᵥ b = 0 := by
  rw [p7w_dot_coe, coe_cross3P, dotProduct_comm]
  exact dot_cross_self _ _

/-- `(a × b) ⬝ᵥ a = 0`（叉积与其第一因子正交）。 -/
private theorem p11w2_cross3_dot_left (a b : V3) : (cross3 a b) ⬝ᵥ a = 0 := by
  rw [p7w_dot_coe, coe_cross3P, dotProduct_comm]
  exact dot_self_cross _ _

/-- `(t • a) ⬝ᵥ b = t * (a ⬝ᵥ b)`（V3 层；经 `p7w_dot_coe` + `smul_dotP`）。 -/
private theorem p11w2_dot_smul_left (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) := by
  rw [p7w_dot_coe, p7w_dot_coe, coe_smulP, smul_dotP]

/-- `(a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c`（V3 层）。 -/
private theorem p11w2_dot_add_left (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c := by
  rw [p7w_dot_coe, p7w_dot_coe, p7w_dot_coe, p10w_coe_addP, add_dotProduct]

/-- 共线三点第 2、3 位交换。 -/
private theorem p11w2_col3_swap {a b c : V3} (h : Collinear3 a b c) : Collinear3 a c b := by
  have hset : ({a, c, b} : Set V3) = {a, b, c} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  show Collinear ℝ ({a, c, b} : Set V3)
  rw [hset]
  exact h

/-- 极扇正性：`0 < (p v) ⬝ᵥ w`（`w ∈ V`、`w ≠ v`、`w ≠ ρ v`）。 -/
private theorem p11w2_polar_pos_dot {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi)
    {v w : V3} (hv : v ∈ V) (hw : w ∈ V) (hwv : w ≠ v) (hwr : w ≠ rhoNode1 FF v) :
    0 < (cross3 v (rhoNode1 FF v)) ⬝ᵥ w := by
  have hsin := GENERIC_LOCAL_FAN_AZIM_POS hcl hedge hg hia v w hv hw hwv hwr
  exact (SIN_AZIM_MUTUAL_CROSS v (rhoNode1 FF v) w).2.1.mp hsin

/-- `affGt {x} {v}` 的射线系数形（严格正）。 -/
private theorem p11w2_gt_single_elim {x v y : V3} (hxv : x ≠ v)
    (h : y ∈ affGt {x} {v}) :
    ∃ a : ℝ, 0 < a ∧ y - x = a • (v - x) := by
  obtain ⟨f, hfin, hvec, hsign, hone⟩ := h
  have htof : hfin.toFinset = ({x, v} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [htof, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton] at hvec hone
  refine ⟨f v, hsign v (by simp), ?_⟩
  have hfx : f x = 1 - f v := by linarith
  rw [hvec, hfx]
  module

/-- 极扇的 `hve` 条件（`FAN_AFF_GT_CONDITION` 前题之二）：单点锥与边锥不交。 -/
theorem p11w2_polar_hve {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    ∀ v ∈ polarV V FF, ∀ e ∈ polarE V FF,
      affGt ({(0:V3)} : Set V3) {v} ∩ affGt ({(0:V3)} : Set V3) e = ∅ := by
  intro v hv e he
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, rfl⟩ := he
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hy1, hy2⟩
  have hpa0 : cross3 a (rhoNode1 FF a) ≠ 0 := P11W_PRIME_NE_ZERO hcl a ha
  have hpb0 : cross3 b (rhoNode1 FF b) ≠ 0 := P11W_PRIME_NE_ZERO hcl b hb
  have hrvaV : rhoNode1 FF a ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 ha
  have hrvbV : rhoNode1 FF b ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hb
  have hpra0 : cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)) ≠ 0 :=
    P11W_PRIME_NE_ZERO hcl (rhoNode1 FF a) hrvaV
  have hprb0 : cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) ≠ 0 :=
    P11W_PRIME_NE_ZERO hcl (rhoNode1 FF b) hrvbV
  have hae : a ≠ rhoNode1 FF a := by
    intro h
    exact hpa0 (by rw [← h]; exact p11w2_cross3_self a)
  have hbe : b ≠ rhoNode1 FF b := by
    intro h
    exact hpb0 (by rw [← h]; exact p11w2_cross3_self b)
  have hpane : cross3 a (rhoNode1 FF a)
      ≠ cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)) := by
    intro h
    exact hae (P11W_PRIME_INJ hcl hedge hg hia a ha (rhoNode1 FF a) hrvaV h)
  have hpbne : cross3 b (rhoNode1 FF b)
      ≠ cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
    intro h
    exact hbe (P11W_PRIME_INJ hcl hedge hg hia b hb (rhoNode1 FF b) hrvbV h)
  obtain ⟨s, hs, hys⟩ := p11w2_gt_single_elim (x := (0:V3)) (v := cross3 a (rhoNode1 FF a))
    (Ne.symm hpa0) hy1
  obtain ⟨t, u, ht, hu, hyt⟩ := p11w2_gt_pair_rel_elim (x := (0:V3))
    (u := cross3 b (rhoNode1 FF b))
    (v := cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
    (Ne.symm hpb0) (Ne.symm hprb0) hpbne hy2
  have hyA : y = s • cross3 a (rhoNode1 FF a) := by
    simpa using hys
  have hyB : y = t • cross3 b (rhoNode1 FF b)
      + u • cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
    simpa using hyt
  -- 点积探针：`ρb`
  have hdot : s * ((cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF b) = 0 := by
    have hL : y ⬝ᵥ rhoNode1 FF b
        = s * ((cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF b) := by
      rw [hyA]
      exact p11w2_dot_smul_left s _ _
    have hR : y ⬝ᵥ rhoNode1 FF b = 0 := by
      rw [hyB, p11w2_dot_add_left, p11w2_dot_smul_left, p11w2_dot_smul_left,
        p11w2_cross3_dot_right, p11w2_cross3_dot_left]
      ring
    rw [hL] at hR
    exact hR
  have hpa_rhob : (cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF b = 0 := by
    rcases mul_eq_zero.mp hdot with h | h
    · exact absurd h hs.ne'
    · exact h
  by_cases h1 : rhoNode1 FF b = a
  · -- 例外一：`ρb = a`（`p a = p(ρb)`）：方程给出 `p b ∥ p(ρb)`
    have hpaeq : cross3 a (rhoNode1 FF a)
        = cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
      rw [h1]
    have hsub : t • cross3 b (rhoNode1 FF b)
        = (s - u) • cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
      have heq : s • cross3 a (rhoNode1 FF a)
          = t • cross3 b (rhoNode1 FF b)
            + u • cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
        rw [← hyA, hyB]
      rw [hpaeq] at heq
      rw [sub_smul]
      exact (eq_sub_iff_add_eq).mpr heq.symm
    have hpb_eq : cross3 b (rhoNode1 FF b)
        = ((s - u) / t) • cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
      have h := congrArg (fun z => t⁻¹ • z) hsub
      rw [smul_smul, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h
      refine h.trans ?_
      rw [div_eq_inv_mul]
    have hcol : Collinear3 (0:V3)
        (cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
        (cross3 b (rhoNode1 FF b)) :=
      (collinear3_iff_smul (v := (0:V3))
        (w := cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
        (w1 := cross3 b (rhoNode1 FF b)) hprb0).mpr
        ⟨(s - u) / t, by rw [hpb_eq, sub_zero, sub_zero]⟩
    exact P11W_PRIME_NCOL hcl hedge hg hia b hb (rhoNode1 FF b) hrvbV hbe
      (p11w2_col3_swap hcol)
  · by_cases h2' : rhoNode1 FF b = rhoNode1 FF a
    · -- 例外二：`ρb = ρa ⟹ b = a`：方程给出 `p b ∥ p a`（= `p ρa`）
      have hba : b = a := w6a_rho_inj h2 hb ha h2'
      rw [hba] at hyB
      have hsub : (s - t) • cross3 a (rhoNode1 FF a)
          = u • cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)) := by
        have heq : s • cross3 a (rhoNode1 FF a)
            = t • cross3 a (rhoNode1 FF a)
              + u • cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)) := by
          rw [← hyA, hyB]
        rw [sub_smul, heq]
        abel
      have hpr_eq : cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a))
          = (u⁻¹ * (s - t)) • cross3 a (rhoNode1 FF a) := by
        have h := congrArg (fun z => u⁻¹ • z) hsub
        rw [smul_smul, smul_smul, inv_mul_cancel₀ hu.ne', one_smul] at h
        exact h.symm
      have hcol : Collinear3 (0:V3) (cross3 a (rhoNode1 FF a))
          (cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a))) :=
        (collinear3_iff_smul (v := (0:V3)) (w := cross3 a (rhoNode1 FF a))
          (w1 := cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)))
          hpa0).mpr ⟨u⁻¹ * (s - t), by rw [hpr_eq, sub_zero, sub_zero]⟩
      exact P11W_PRIME_NCOL hcl hedge hg hia a ha (rhoNode1 FF a) hrvaV hae hcol
    · -- 一般情形：正性
      have hpos : 0 < (cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF b :=
        p11w2_polar_pos_dot hcl hedge hg hia ha hrvbV h1 h2'
      exact absurd hpa_rhob hpos.ne'

/-- 极扇的 `hee` 条件（`FAN_AFF_GT_CONDITION` 前题之三）：两条不同极边锥不交。 -/
theorem p11w2_polar_hee {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    ∀ e1 ∈ polarE V FF, ∀ e2 ∈ polarE V FF, e1 ≠ e2 →
      affGt ({(0:V3)} : Set V3) e1 ∩ affGt ({(0:V3)} : Set V3) e2 = ∅ := by
  intro e1 he1 e2 he2 hne
  obtain ⟨a, ha, rfl⟩ := he1
  obtain ⟨b, hb, rfl⟩ := he2
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨hy1, hy2⟩
  have hpa0 : cross3 a (rhoNode1 FF a) ≠ 0 := P11W_PRIME_NE_ZERO hcl a ha
  have hpb0 : cross3 b (rhoNode1 FF b) ≠ 0 := P11W_PRIME_NE_ZERO hcl b hb
  have hrvaV : rhoNode1 FF a ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 ha
  have hrvbV : rhoNode1 FF b ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hb
  have hpra0 : cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)) ≠ 0 :=
    P11W_PRIME_NE_ZERO hcl (rhoNode1 FF a) hrvaV
  have hprb0 : cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) ≠ 0 :=
    P11W_PRIME_NE_ZERO hcl (rhoNode1 FF b) hrvbV
  have hae : a ≠ rhoNode1 FF a := by
    intro h
    exact hpa0 (by rw [← h]; exact p11w2_cross3_self a)
  have hbe : b ≠ rhoNode1 FF b := by
    intro h
    exact hpb0 (by rw [← h]; exact p11w2_cross3_self b)
  have hpane : cross3 a (rhoNode1 FF a)
      ≠ cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)) := by
    intro h
    exact hae (P11W_PRIME_INJ hcl hedge hg hia a ha (rhoNode1 FF a) hrvaV h)
  have hpbne : cross3 b (rhoNode1 FF b)
      ≠ cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
    intro h
    exact hbe (P11W_PRIME_INJ hcl hedge hg hia b hb (rhoNode1 FF b) hrvbV h)
  obtain ⟨s, t, hs, ht, hys⟩ := p11w2_gt_pair_rel_elim (x := (0:V3))
    (u := cross3 a (rhoNode1 FF a))
    (v := cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)))
    (Ne.symm hpa0) (Ne.symm hpra0) hpane hy1
  obtain ⟨u, v, hu, hv, hyt⟩ := p11w2_gt_pair_rel_elim (x := (0:V3))
    (u := cross3 b (rhoNode1 FF b))
    (v := cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
    (Ne.symm hpb0) (Ne.symm hprb0) hpbne hy2
  have hyA : y = s • cross3 a (rhoNode1 FF a)
      + t • cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)) := by
    simpa using hys
  have hyB : y = u • cross3 b (rhoNode1 FF b)
      + v • cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)) := by
    simpa using hyt
  -- 点积探针：`ρa`
  have hdot : u * ((cross3 b (rhoNode1 FF b)) ⬝ᵥ rhoNode1 FF a)
      + v * ((cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
        ⬝ᵥ rhoNode1 FF a) = 0 := by
    have hA : y ⬝ᵥ rhoNode1 FF a
        = s * ((cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF a)
          + t * ((cross3 (rhoNode1 FF a) (rhoNode1 FF (rhoNode1 FF a)))
            ⬝ᵥ rhoNode1 FF a) := by
      rw [hyA, p11w2_dot_add_left, p11w2_dot_smul_left, p11w2_dot_smul_left]
    have hB : y ⬝ᵥ rhoNode1 FF a
        = u * ((cross3 b (rhoNode1 FF b)) ⬝ᵥ rhoNode1 FF a)
          + v * ((cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
            ⬝ᵥ rhoNode1 FF a) := by
      rw [hyB, p11w2_dot_add_left, p11w2_dot_smul_left, p11w2_dot_smul_left]
    rw [hA, p11w2_cross3_dot_right, p11w2_cross3_dot_left, mul_zero, mul_zero,
      add_zero] at hB
    exact hB.symm
  by_cases hab : a = b
  · subst hab
    exact absurd rfl hne
  · by_cases h2' : rhoNode1 FF a = rhoNode1 FF b
    · exact absurd (w6a_rho_inj h2 ha hb h2') hab
    · by_cases h3 : rhoNode1 FF a = b
      · -- 相邻一：`b = ρa`，换探针 `ρ(ρa)`
        have hρρaV : rhoNode1 FF (rhoNode1 FF a) ∈ V :=
          LOFA_IN_V_SO_DO_RHO_NODE_V h2 hrvaV
        have hA : y ⬝ᵥ rhoNode1 FF (rhoNode1 FF a)
            = s * ((cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF (rhoNode1 FF a)) := by
          rw [hyA, p11w2_dot_add_left, p11w2_dot_smul_left, p11w2_dot_smul_left,
            p11w2_cross3_dot_right, mul_zero, add_zero]
        have hB : y ⬝ᵥ rhoNode1 FF (rhoNode1 FF a) = 0 := by
          rw [hyB, p11w2_dot_add_left, p11w2_dot_smul_left, p11w2_dot_smul_left]
          rw [← h3]
          rw [p11w2_cross3_dot_right, p11w2_cross3_dot_left, mul_zero, mul_zero,
            add_zero]
        have hpa_rra : (cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF (rhoNode1 FF a) = 0 := by
          have h : s * ((cross3 a (rhoNode1 FF a))
              ⬝ᵥ rhoNode1 FF (rhoNode1 FF a)) = 0 := by
            rw [← hA, hB]
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' hs.ne'
          · exact h'
        have hsem : rhoNode1 FF (rhoNode1 FF a) ≠ a :=
          LOCAL_FAN_IMP_NOT_SEMI_IDE h2 ha
        have hrra : rhoNode1 FF (rhoNode1 FF a) ≠ rhoNode1 FF a := by
          intro h
          have h' : a = rhoNode1 FF a := w6a_rho_inj h2 ha hrvaV h.symm
          exact hae h'
        have hpos := p11w2_polar_pos_dot hcl hedge hg hia ha hρρaV hsem hrra
        exact absurd hpa_rra hpos.ne'
      · by_cases h4 : rhoNode1 FF a = rhoNode1 FF (rhoNode1 FF b)
        · -- 相邻二：`a = ρb`，`p(ρb) = p a` 消去 hdot 第二项
          have hab' : a = rhoNode1 FF b := w6a_rho_inj h2 ha hrvbV h4
          have hprb_eq : cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b))
              = cross3 a (rhoNode1 FF a) := by
            rw [← h4, ← hab']
          have hz : (cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
              ⬝ᵥ rhoNode1 FF a = (cross3 a (rhoNode1 FF a)) ⬝ᵥ rhoNode1 FF a := by
            rw [hprb_eq]
          have hdot' : u * ((cross3 b (rhoNode1 FF b)) ⬝ᵥ rhoNode1 FF a) = 0 := by
            rw [hz, p11w2_cross3_dot_right, mul_zero, add_zero] at hdot
            exact hdot
          have hpb_ra : (cross3 b (rhoNode1 FF b)) ⬝ᵥ rhoNode1 FF a = 0 := by
            rcases mul_eq_zero.mp hdot' with h' | h'
            · exact absurd h' hu.ne'
            · exact h'
          have h3' : rhoNode1 FF a ≠ b := by
            intro h
            have h'' : rhoNode1 FF (rhoNode1 FF b) = b := by
              rw [← h4]
              exact h
            exact LOCAL_FAN_IMP_NOT_SEMI_IDE h2 hb h''
          have h2'' : rhoNode1 FF a ≠ rhoNode1 FF b := by
            intro h
            exact hab (w6a_rho_inj h2 ha hb h)
          have hpos := p11w2_polar_pos_dot hcl hedge hg hia hb hrvaV h3' h2''
          exact absurd hpb_ra hpos.ne'
        · -- 一般情形：两项都正
          have hp1 : 0 < (cross3 b (rhoNode1 FF b)) ⬝ᵥ rhoNode1 FF a :=
            p11w2_polar_pos_dot hcl hedge hg hia hb hrvaV h3 h2'
          have hp2 : 0 < (cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
              ⬝ᵥ rhoNode1 FF a :=
            p11w2_polar_pos_dot hcl hedge hg hia hrvbV hrvaV h2' h4
          have hpos : 0 < u * ((cross3 b (rhoNode1 FF b)) ⬝ᵥ rhoNode1 FF a)
              + v * ((cross3 (rhoNode1 FF b) (rhoNode1 FF (rhoNode1 FF b)))
                ⬝ᵥ rhoNode1 FF a) := by
            have h1' := mul_pos hu hp1
            have h2'' := mul_pos hv hp2
            linarith
          exact absurd hdot hpos.ne'

/-- `⋃₀ E' ⊆ V'`（`FAN_AFF_GT_CONDITION` 的 `hun` 前题）。 -/
theorem p11w2_polar_unions {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    ⋃₀ polarE V FF ⊆ polarV V FF := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := hx
  obtain ⟨v, hv, rfl⟩ := he
  have h2 : localFan_p2 V E FF := w6a_to_p2 hcl.1 hedge
  rcases Set.mem_insert_iff.mp hxe with h | h
  · exact ⟨v, hv, h.symm⟩
  · rw [Set.mem_singleton_iff] at h
    exact ⟨rhoNode1 FF v, LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv, h.symm⟩

/-- **`FAN 0 V' E'`**（BGMIFTE 结论 1 的 FAN 前件）：`P11W_POLAR_FAN_BASIC`
四件 + `p11w2_polar_hvs/hve/hee` + `FAN_AFF_GT_CONDITION`。 -/
theorem p11w2_polar_FAN {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    FAN (0:V3) (polarV V FF) (polarE V FF) := by
  have hbasic := P11W_POLAR_FAN_BASIC hcl hedge hg hia
  have hG : Graph (polarE V FF) := by
    have h := hbasic.1
    rwa [p11w2_polarFan_components] at h
  have hf1 : fan1 (0:V3) (polarV V FF) (polarE V FF) := by
    have h := hbasic.2.1
    rwa [p11w2_polarFan_components] at h
  have hf2 : fan2 (0:V3) (polarV V FF) (polarE V FF) := by
    have h := hbasic.2.2.1
    rwa [p11w2_polarFan_components] at h
  have hf6 : fan6 (0:V3) (polarV V FF) (polarE V FF) := by
    have h := hbasic.2.2.2
    rwa [p11w2_polarFan_components] at h
  refine ⟨p11w2_polar_unions hcl hedge, hG, hf1, hf2, hf6, ?_⟩
  refine FAN7_AFF_GT_CONDITION 0 (polarV V FF) (polarE V FF) hG hf2 ?_ ?_ ?_ ?_
  · intro e he
    refine ⟨fun z hz => p11w2_polar_unions hcl hedge
      (Set.subset_sUnion_of_mem he hz), ?_⟩
    intro h0
    obtain ⟨v, hv, rfl⟩ := he
    rcases Set.mem_insert_iff.mp h0 with h | h
    · exact P11W_PRIME_NE_ZERO hcl v hv h.symm
    · rw [Set.mem_singleton_iff] at h
      exact P11W_PRIME_NE_ZERO hcl (rhoNode1 FF v)
        (LOFA_IN_V_SO_DO_RHO_NODE_V (w6a_to_p2 hcl.1 hedge) hv) h.symm
  · exact p11w2_polar_hvs hcl hedge hg hia
  · exact p11w2_polar_hve hcl hedge hg hia
  · exact p11w2_polar_hee hcl hedge hg hia

end W11b2Kit2


/-- HOL `WSEWPCH` (polar_fan.hl:2213): the fan perimeter of a convex
local fan is at most `2 * pi`. -/
theorem WSEWPCH {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : fanPerimeter V E FF ≤ 2 * Real.pi := by
  sorry

end Kepler.Text
