/-
Port of the HOL Light Flyspeck packing theory, `pack1` + `pack2` slices:
finiteness of packings inside bounded balls, the floor-lattice injection
`map3`, and the basic geometry of open and closed Voronoi cells.

HOL sources (persistent copies under `lean/scripts/packing/`):
- `pack1.hl` (Nguyen Tat Thang, 2010-02-09): `map3`, the `Vol1` stand-ins
  `int_ball`/`hinhcau_ball`/`finite_int_ball`/`FINITE_IMAGE_INJ`, the small
  real lemmas `bound_square`/`cauchy_ineq`/`bdt_*`, `map3_define`,
  `floor_ineq`, `inj_map3`, Lemma 5.1 `KIUMVTC`, `voronoi_open`, `bis`,
  `nua_kg`, `saturated`, convexity/boundedness/openness of open cells, and
  the density chain `measure_ineq_lm53_*`, `ineq_lm5_3_step*`, `JGXZYGW`.
- `pack2.hl` (John Harrison, 2010-03-16): `PACKING`, closed cells
  `voronoi_closed` (encoded here as `voronoi`), `bis_le`, `bis_lt`,
  the closed/open transfer theorems (`CLOSURE_VORONOI_OPEN`,
  `MEASURE_VORONOI_CLOSED_OPEN`, ...) and the closed-cell density chain.

Encoding notes (gaps / decisions):
- HOL `real^3` ↔ `Kepler.Space3 = EuclideanSpace ℝ (Fin 3)`; coordinates are
  read through the coercion `(x : Fin 3 → ℝ)`; `lambda i. ...` ↔
  `WithLp.toLp 2 (fun i => ...)`; `dot` ↔ `⬝ᵥ` (`Kepler.Geom.inner_eq_dot`).
- HOL `packing` (`Sphere.packing`) is identical in meaning to `Kepler.Packing`
  (Kepler/Statement.lean:35). The bridge is `PACKING` below (`Iff.rfl`) plus
  `packing_iff_ne` for the contrapositive shape. No new predicate was needed.
- `int_ball`, `hinhcau_ball`, `finite_int_ball`, `FINITE_IMAGE_INJ` are only
  referenced from the Flyspeck volume chapter (`Vol1`, not present under
  `lean/scripts/`); they are re-declared here from their use in pack1.hl
  (:21-:24, :112, :140-:145): `hinhcau_ball c r` is the metric ball,
  `int_ball c r` the integer-coordinate points of it.
- HOL `voronoi_closed` (pack2.hl:30) is encoded as `voronoi`; the open cell
  keeps the name `voronoi_open` (pack1.hl:153).
- HOL `INJ f s t` ↔ `Set.MapsTo f s t ∧ Set.InjOn f s` (inj_map3).
- HOL `measure s` (a real number) ↔ `(volume s).toReal`; *negligibility* is
  stated as `volume s = 0` in `ℝ≥0∞`, matching null statements.
- HOL `sum s f` over a set ↔ `∑ v ∈ s.toFinset, f v` (finite for packings by
  `KIUMVTC`; HOL's support convention on infinite sets is never exercised in
  the intended instances).
- HOL set-builder images `{f w v | v IN t /\ w = S}` ↔ `⋃ v ∈ t, f S v`
  (unions) or binder set-builders / `Set.image` (images).
- HOL `measurable s` ↔ `MeasurableSet s`; `bounded s` ↔ `Bornology.IsBounded`;
  `compact s` ↔ `IsCompact s`.
- pack1/pack2 name collisions (`DRUQUFE`, `convex_voronoi`, `bound_voronoi`,
  `finite_voronoi2`, `measurable_voronoi`, `measurable_unions_voronoi`,
  `measure_unions_sum_voronoi`, `ineq_lm5_3_step3`,
  `finite_set_voronoi_center_in_ball`) are resolved by suffixing the pack2
  (closed-cell) versions with `_closed`. `Pack2.KIUMVTC` (the `0 ≤ r`-free
  variant) is `KIUMVTC'`; `Pack1.KIUMVTC` keeps its name.
- `open_voronoi` is proved directly by a uniform-gap argument over the finite
  set of centers within distance 4 of `v`; the HL detour through
  `not_open_voronoi1/2/3` is kept as statements, with `not_open_voronoi1`
  (a sequential-compactness pigeonhole) left as a `sorry` straggler.
- `ineq_lm5_3_step4`'s witness is `63 * π / √18 + 4 * c / √32`.
- Heavy stragglers left as `sorry`: `VORONOI_CLOSED_AS_FINITE_INTERSECTION`
  (needs `HALFLINE_INTER_COMPACT_SEGMENT`, absent from Mathlib) and its
  polyhedrality/polytope corollaries, the partition of space by closed cells
  (needs a closest-point projection theorem), `not_open_voronoi1`,
  `INTERIOR_VORONOI_CLOSED_INTERIOR` (needs `int (cl X) = int X` for convex
  `X` with empty interior — the proper-subspace argument; Mathlib only has
  the nonempty-interior case), `measure_ineq_lm53_2` and `JGXZYGW`.
-/

import Kepler.Text.Polytope
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Metric MeasureTheory Filter Topology Classical

noncomputable section

local instance : DecidableEq Space3 := Classical.decEq Space3

/-! ## Vol1 stand-ins: lattice points in a ball -/

/-- HOL `Vol1.hinhcau_ball` (used in pack1.hl:22): the ball `ball c r`. -/
def hinhcau_ball (c : Space3) (r : ℝ) : Set Space3 := Metric.ball c r

/-- HOL `Vol1.int_ball` (pack1.hl:21): integer-coordinate points of
`hinhcau_ball c r`; HOL `integer x` on `real^3` means all coordinates are
integers. -/
def int_ball (c : Space3) (r : ℝ) : Set Space3 :=
  {x : Space3 | (∀ i, ∃ n : ℤ, ((x : Fin 3 → ℝ) i) = (n : ℝ)) ∧ x ∈ hinhcau_ball c r}

/-- HOL `Vol1.FINITE_IMAGE_INJ` (pack1.hl:24). -/
theorem FINITE_IMAGE_INJ {α β : Type*} {s : Set α} {f : α → β}
    (hs : s.Finite) (hinj : Set.InjOn f s) : (f '' s).Finite :=
  hs.image f

/-- A set on which `f` is injective and whose image is finite is itself
finite (finiteness transfer used in `KIUMVTC`). -/
theorem finite_of_injOn_image {α β : Type*} {s : Set α} {f : α → β}
    (hinj : Set.InjOn f s) (hi : (f '' s).Finite) : s.Finite :=
  (Set.finite_image_iff hinj).mp hi

/-- `‖x‖² = Σᵢ xᵢ²` for `x : Space3`. -/
theorem norm_sq_eq_sum_three (x : Space3) : ‖x‖ ^ 2 = ∑ i : Fin 3, ((x : Fin 3 → ℝ) i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Coordinate of a difference. -/
theorem coe_sub_three (a b : Space3) (i : Fin 3) :
    (((a - b : Space3) : Fin 3 → ℝ) i) = (((a : Fin 3 → ℝ) i) - ((b : Fin 3 → ℝ) i)) := rfl

/-- Squared norm of a difference via coordinates. -/
theorem norm_sq_eq_sum_three_sub (a b : Space3) :
    ‖a - b‖ ^ 2 = ∑ i : Fin 3, (((a : Fin 3 → ℝ) i) - ((b : Fin 3 → ℝ) i)) ^ 2 :=
  norm_sq_eq_sum_three (a - b)

/-- HOL `Vol1.finite_int_ball` (pack1.hl:23): the lattice points in a ball
form a finite set. -/
theorem finite_int_ball (c : Space3) (r : ℝ) : (int_ball c r).Finite := by
  classical
  set B : ℝ := r + ‖c‖ + 1 with hBdef
  set box : Set (Fin 3 → ℤ) :=
    Set.univ.pi (fun _ : Fin 3 => Set.Ico (Int.floor (-B)) (Int.ceil B)) with hboxdef
  have hboxfin : box.Finite :=
    Set.Finite.pi (fun _ : Fin 3 => Set.finite_Ico _ _)
  set f : Space3 → (Fin 3 → ℤ) := fun x i => Int.floor ((x : Fin 3 → ℝ) i) with hfdef
  have hfloor_eq : ∀ z : ℝ, (∃ n : ℤ, z = (n : ℝ)) → Int.floor z = z := by
    rintro z ⟨n, rfl⟩; simp
  have hcomp : ∀ (z : Space3) (i : Fin 3), ((z : Fin 3 → ℝ) i) ^ 2 ≤ ‖z‖ ^ 2 := by
    intro z i
    rw [norm_sq_eq_sum_three z]
    exact Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg _) (Finset.mem_univ i)
  have hinj : Set.InjOn f (int_ball c r) := by
    intro x hx y hy hxy
    obtain ⟨hxlat, -⟩ := hx
    obtain ⟨hylat, -⟩ := hy
    have hxy' : ((x : Fin 3 → ℝ)) = ((y : Fin 3 → ℝ)) := by
      funext i
      have hxi : ((x : Fin 3 → ℝ) i) = ((Int.floor ((x : Fin 3 → ℝ) i) : ℤ) : ℝ) :=
        (hfloor_eq _ (hxlat i)).symm
      have hyi : ((y : Fin 3 → ℝ) i) = ((Int.floor ((y : Fin 3 → ℝ) i) : ℤ) : ℝ) :=
        (hfloor_eq _ (hylat i)).symm
      have hi := congrFun hxy i
      simp only [hfdef] at hi
      rw [hxi, hyi, hi]
    calc x = WithLp.toLp 2 ((x : Fin 3 → ℝ)) := (WithLp.toLp_ofLp 2 x).symm
      _ = WithLp.toLp 2 ((y : Fin 3 → ℝ)) := by rw [hxy']
      _ = y := WithLp.toLp_ofLp 2 y
  have himage : f '' (int_ball c r) ⊆ box := by
    rintro z ⟨x, hxmem, rfl⟩
    obtain ⟨hxlat, hxball⟩ := hxmem
    have hxb : ‖x - c‖ < r := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hxball
    have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg (x - c)) hxb
    refine Set.mem_pi.mpr fun i _ => ?_
    have hcabs : |((c : Fin 3 → ℝ) i)| ≤ ‖c‖ := by
      rw [abs_le]
      have h1 : ((c : Fin 3 → ℝ) i) ^ 2 ≤ ‖c‖ ^ 2 := hcomp c i
      have h2 : 0 ≤ ‖c‖ := norm_nonneg c
      have h3 : 0 ≤ |((c : Fin 3 → ℝ) i)| := abs_nonneg _
      constructor <;> nlinarith
    have hxabs : |((x : Fin 3 → ℝ) i) - ((c : Fin 3 → ℝ) i)| < r := by
      rw [abs_lt]
      have h1 : ((x : Fin 3 → ℝ) i - (c : Fin 3 → ℝ) i) ^ 2 ≤ ‖x - c‖ ^ 2 := hcomp (x - c) i
      have h2 : ‖x - c‖ ^ 2 < r ^ 2 := (sq_lt_sq₀ (norm_nonneg (x - c)) hrpos.le).mpr hxb
      have h3 : ((x : Fin 3 → ℝ) i - (c : Fin 3 → ℝ) i) ^ 2 < r ^ 2 := lt_of_le_of_lt h1 h2
      constructor <;> nlinarith
    have hxin : ((x : Fin 3 → ℝ) i) ∈ Set.Ioo (-B) B := by
      rw [Set.mem_Ioo]
      have hci := abs_le.mp hcabs
      have hxi := abs_lt.mp hxabs
      constructor <;> linarith
    have hlo : Int.floor (-B) ≤ Int.floor ((x : Fin 3 → ℝ) i) :=
      Int.floor_le_floor hxin.1.le
    have hhi : Int.floor ((x : Fin 3 → ℝ) i) < Int.ceil B := by
      have h1 : ((Int.floor ((x : Fin 3 → ℝ) i) : ℤ) : ℝ) < ((Int.ceil B : ℤ) : ℝ) := by
        have ha : ((Int.floor ((x : Fin 3 → ℝ) i) : ℤ) : ℝ) ≤ ((x : Fin 3 → ℝ) i) :=
          Int.floor_le _
        have hb : B ≤ ((Int.ceil B : ℤ) : ℝ) := Int.le_ceil B
        linarith [hxin.2]
      exact Int.cast_lt.mp h1
    rw [hfdef]
    exact Set.mem_Ico.mpr ⟨hlo, hhi⟩
  have himfin : (f '' (int_ball c r)).Finite := hboxfin.subset himage
  exact finite_of_injOn_image hinj himfin

/-! ## The packing predicate: bridge to `Kepler.Packing` -/

/-- HOL `Pack2.PACKING` (pack2.hl:21): HOL `Sphere.packing` equals the
`dist < 2 → u = v` reading, i.e. exactly `Kepler.Packing`
(Kepler/Statement.lean:35). -/
theorem PACKING (S : Set Space3) :
    Packing S ↔ ∀ u v : Space3, u ∈ S → v ∈ S → dist u v < 2 → u = v := by
  unfold Packing
  constructor
  · intro h u v hu hv hc
    exact h u hu v hv hc
  · intro h u v hu hv hc
    exact h u hu v hv hc

/-- HOL `Sphere.packing`, contrapositive form (`Packing.dist_ge_two`). -/
theorem packing_iff_ne (S : Set Space3) :
    Packing S ↔ ∀ u v : Space3, u ∈ S → v ∈ S → u ≠ v → 2 ≤ dist u v := by
  rw [PACKING S]
  constructor
  · intro h u v hu hv hne
    refine le_of_not_gt ?_
    intro hc
    exact hne (h u v hu hv hc)
  · intro h u v hu hv hc
    by_contra hne
    exact absurd (h u v hu hv hne) (not_le.mpr hc)

/-! ## Small real lemmas (pack1.hl:34-:109) -/

/-- HOL `bound_square` (pack1.hl:34). -/
theorem bound_square (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : b ^ 2 ≤ max (a ^ 2) (c ^ 2) := by
  rcases le_total 0 b with hb | hb
  · have h : b ^ 2 ≤ c ^ 2 := by nlinarith
    linarith [h, le_max_right (a ^ 2) (c ^ 2)]
  · have h : b ^ 2 ≤ a ^ 2 := by nlinarith
    linarith [h, le_max_left (a ^ 2) (c ^ 2)]

/-- HOL `cauchy_ineq` (pack1.hl:39). -/
theorem cauchy_ineq (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- HOL `bdt_emveque` (pack1.hl:42). -/
theorem bdt_emveque (r : ℝ) : 0 ≤ 8 * r ^ 2 + 6 := by nlinarith

/-- HOL `norm_abs` (pack1.hl:48). -/
theorem norm_abs (x : Space3) : ‖x‖ = |‖x‖| := (abs_of_nonneg (norm_nonneg x)).symm

/-- HOL `bp_bdt` (pack1.hl:50). -/
theorem bp_bdt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a < b ↔ a ^ 2 < b ^ 2) :=
  (sq_lt_sq₀ ha hb).symm

/-- HOL `bdt_emnguchua` (pack1.hl:54). -/
theorem bdt_emnguchua (k : ℝ) :
    ((Int.floor (2 * k) : ℤ) : ℝ) ^ 2 ≤ 2 * (4 * k ^ 2 + 1) := by
  set f := ((Int.floor (2 * k) : ℤ) : ℝ) with hfdef
  have h1 : 2 * k - 1 < f := by
    rw [hfdef]
    linarith [Int.lt_floor_add_one (2 * k)]
  have h2 : f ≤ 2 * k := Int.floor_le (2 * k)
  rcases lt_or_ge f 0 with hneg | hge
  · have hk : k < 1 / 2 := by linarith
    have hb2 : 0 ≤ -f := by linarith
    have hb3 : 0 ≤ 1 - 2 * k := by linarith
    have hlt : (-f) ^ 2 < (1 - 2 * k) ^ 2 := (sq_lt_sq₀ hb2 hb3).mpr (by linarith)
    rw [neg_sq] at hlt
    nlinarith [sq_nonneg (2 * k + 1), hlt]
  · have hsq : f ^ 2 ≤ (2 * k) ^ 2 := by nlinarith
    rw [show (2 * k) ^ 2 = 4 * k ^ 2 from by ring] at hsq
    nlinarith [sq_nonneg k]

/-- HOL `floor_ineq` (pack1.hl:102). -/
theorem floor_ineq (x y : ℝ) (h : Int.floor x = Int.floor y) : |x - y| < 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  rw [← h] at h3 h4
  rw [abs_lt]
  constructor <;> linarith

/-- HOL `bdt_canbatrenbon` (pack1.hl:108). -/
theorem bdt_canbatrenbon : Real.sqrt (3 / 4) < 2 := by
  calc Real.sqrt (3 / 4) < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    _ = 2 := by norm_num

/-! ## The floor-lattice map `map3` (pack1.hl:32-:145) -/

/-- HOL `map3` (pack1.hl:32): `(map3) x p = lambda i. floor(&2 * (x$i - p$i))`;
used as `map3 p v` with `p` the fixed point and `v` the moving center. -/
def map3 (x p : Space3) : Space3 :=
  WithLp.toLp 2 fun i => ((Int.floor (2 * (((x : Fin 3 → ℝ) i) - ((p : Fin 3 → ℝ) i)))) : ℝ)

theorem map3_apply (x p : Space3) (i : Fin 3) :
    ((map3 x p : Fin 3 → ℝ) i) =
      ((Int.floor (2 * (((x : Fin 3 → ℝ) i) - ((p : Fin 3 → ℝ) i)))) : ℝ) := rfl

/-- HOL `map3_define` (pack1.hl:71): `map3` sends a ball of radius `r` into
the lattice points of the ball of radius `√(8r² + 6)` about the origin. -/
theorem map3_define (v p : Space3) (r : ℝ) (hr : 0 ≤ r) (hv : v ∈ Metric.ball p r) :
    map3 p v ∈ Metric.ball 0 (Real.sqrt (8 * r ^ 2 + 6)) := by
  rw [Metric.mem_ball, dist_zero_right]
  have hvp : ‖v - p‖ < r := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hv
  have hcoord : ∀ i : Fin 3,
      ((map3 p v : Fin 3 → ℝ) i) ^ 2 ≤
        2 * (4 * (((p : Fin 3 → ℝ) i) - ((v : Fin 3 → ℝ) i)) ^ 2 + 1) := by
    intro i
    rw [map3_apply]
    exact bdt_emnguchua _
  have hnorm : ‖map3 p v‖ ^ 2 ≤ 8 * ‖v - p‖ ^ 2 + 6 := by
    have hcoe := norm_sq_eq_sum_three_sub v p
    calc ‖map3 p v‖ ^ 2 = ∑ i, ((map3 p v : Fin 3 → ℝ) i) ^ 2 :=
          norm_sq_eq_sum_three (map3 p v)
      _ ≤ ∑ i, 2 * (4 * (((p : Fin 3 → ℝ) i) - ((v : Fin 3 → ℝ) i)) ^ 2 + 1) :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = ∑ i, (8 * (((p : Fin 3 → ℝ) i) - ((v : Fin 3 → ℝ) i)) ^ 2 + 2) := by
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 8 * (∑ i, (((p : Fin 3 → ℝ) i) - ((v : Fin 3 → ℝ) i)) ^ 2) + 6 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
            Finset.card_univ, Fintype.card_fin]
          norm_num
      _ = 8 * ‖v - p‖ ^ 2 + 6 := by
          have hswap : ∑ i, (((p : Fin 3 → ℝ) i) - ((v : Fin 3 → ℝ) i)) ^ 2 =
              ∑ i, (((v : Fin 3 → ℝ) i) - ((p : Fin 3 → ℝ) i)) ^ 2 :=
            Finset.sum_congr rfl fun i _ => by ring
          rw [hswap, hcoe]
  have hbound : ‖map3 p v‖ ^ 2 < 8 * r ^ 2 + 6 := by
    have hq : ‖v - p‖ ^ 2 < r ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg (v - p)) (by linarith)).mpr hvp
    calc ‖map3 p v‖ ^ 2 ≤ 8 * ‖v - p‖ ^ 2 + 6 := hnorm
      _ < 8 * r ^ 2 + 6 := by linarith
  exact Real.lt_sqrt (norm_nonneg _) |>.mpr hbound

/-- HOL `inj_map3` (pack1.hl:112): `map3 p` is injective on `S ∩ ball p r`
and lands in `int_ball 0 (√(8r² + 6))`. HOL `INJ f s t` is split into
`Set.MapsTo` and `Set.InjOn`. -/
theorem inj_map3 (p : Space3) (r : ℝ) (S : Set Space3) (hr : 0 ≤ r) (hV : Packing S) :
    Set.MapsTo (map3 p) (S ∩ Metric.ball p r) (int_ball 0 (Real.sqrt (8 * r ^ 2 + 6))) ∧
      Set.InjOn (map3 p) (S ∩ Metric.ball p r) := by
  constructor
  · rintro x ⟨hxS, hxb⟩
    refine ⟨fun i => ⟨_, by rw [map3_apply]⟩, ?_⟩
    exact map3_define x p r hr hxb
  · intro x hx y hy hxy
    obtain ⟨hxS, -⟩ := hx
    obtain ⟨hyS, -⟩ := hy
    by_contra hne
    have hcoord : ∀ i : Fin 3, -(1 / 2) < ((y : Fin 3 → ℝ) i) - ((x : Fin 3 → ℝ) i) ∧
        ((y : Fin 3 → ℝ) i) - ((x : Fin 3 → ℝ) i) < 1 / 2 := by
      intro i
      have h2 : ((map3 p x : Fin 3 → ℝ) i) = ((map3 p y : Fin 3 → ℝ) i) := by rw [hxy]
      rw [map3_apply, map3_apply] at h2
      have h1 := floor_ineq _ _ (Int.cast_injective h2)
      rw [abs_lt] at h1
      constructor <;> linarith
    have hlt : ∀ i : Fin 3, (((y : Fin 3 → ℝ) i) - ((x : Fin 3 → ℝ) i)) ^ 2 < 1 / 4 := by
      intro i
      obtain ⟨h4, h5⟩ := hcoord i
      nlinarith
    have hsq : ‖y - x‖ ^ 2 < 3 / 4 := by
      rw [norm_sq_eq_sum_three]
      have hcoe : ∀ i, (((y - x : Space3) : Fin 3 → ℝ) i) =
          ((y : Fin 3 → ℝ) i) - ((x : Fin 3 → ℝ) i) := by
        intro i; rfl
      calc ∑ i, (((y - x : Space3) : Fin 3 → ℝ) i) ^ 2 =
            ∑ i, (((y : Fin 3 → ℝ) i) - ((x : Fin 3 → ℝ) i)) ^ 2 := by
            exact Finset.sum_congr rfl fun i _ => by rw [hcoe i]
        _ < ∑ i : Fin 3, ((1 : ℝ) / 4) :=
            Finset.sum_lt_sum (fun i _ => le_of_lt (hlt i)) ⟨0, Finset.mem_univ 0, hlt 0⟩
        _ = 3 / 4 := by ring
    have hnorm : ‖y - x‖ < Real.sqrt (3 / 4) := Real.lt_sqrt (norm_nonneg _) |>.mpr hsq
    have hdist : dist x y < 2 := by
      rw [dist_eq_norm, norm_sub_rev]
      linarith [hnorm, bdt_canbatrenbon]
    exact hne (hV x hxS y hyS hdist)

/-- HOL Lemma 5.1 `KIUMVTC` (pack1.hl:140): a packing inside a ball is
finite. -/
theorem KIUMVTC (p : Space3) (r : ℝ) (S : Set Space3) (hr : 0 ≤ r) (hV : Packing S) :
    (S ∩ Metric.ball p r).Finite := by
  classical
  have hinj := inj_map3 p r S hr hV
  have himfin : ((map3 p) '' (S ∩ Metric.ball p r)).Finite :=
    (finite_int_ball 0 (Real.sqrt (8 * r ^ 2 + 6))).subset hinj.1.image_subset
  exact finite_of_injOn_image hinj.2 himfin

/-- HOL `Pack2.KIUMVTC` (pack2.hl:38): the same without the `0 ≤ r`
hypothesis. -/
theorem KIUMVTC' (p : Space3) (r : ℝ) (S : Set Space3) (hV : Packing S) :
    (S ∩ Metric.ball p r).Finite := by
  classical
  by_cases hr : 0 ≤ r
  · exact KIUMVTC p r S hr hV
  · have : Metric.ball p r = ∅ := Metric.ball_eq_empty.mpr (le_of_not_ge hr)
    rw [this, Set.inter_empty]
    exact Set.finite_empty


/-- Coercion-safe inner identity for perturbations toward `v`. -/
theorem inner_add_smul_right' (A x v : Space3) (t : ℝ) :
    inner ℝ A (x + t • (v - x)) = inner ℝ A x + t * (inner ℝ A v - inner ℝ A x) := by
  rw [inner_add_right, real_inner_smul_right, inner_sub_right]

/-- Coercion-safe inner identity for perturbations away from `x`. -/
theorem inner_sub_smul_right' (A x v u : Space3) (t : ℝ) :
    inner ℝ A (x - t • (v - u)) = inner ℝ A x - t * (inner ℝ A v - inner ℝ A u) := by
  rw [inner_sub_right, real_inner_smul_right, inner_sub_right]

/-- Coercion-safe inner identity. -/
theorem inner_sub_smul_right'' (A x w : Space3) (t : ℝ) :
    inner ℝ A (x - t • w) = inner ℝ A x - t * inner ℝ A w := by
  rw [inner_sub_right, real_inner_smul_right]

/-- Coercion-safe norm identity. -/
theorem norm_add_smul (x v : Space3) (t : ℝ) (ht : 0 ≤ t) :
    ‖x + t • (v - x) - x‖ = t * ‖v - x‖ := by
  have h1 : x + t • (v - x) - x = t • (v - x) := by rw [add_sub_cancel_left]
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

/-- Coercion-safe norm identity. -/
theorem norm_sub_smul (x v u : Space3) (t : ℝ) (ht : 0 ≤ t) :
    ‖x - t • (v - u) - x‖ = t * ‖v - u‖ := by
  have h1 : x - t • (v - u) - x = -(t • (v - u)) := by abel
  rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

/-- The bisector functional at `v`. -/
theorem bisector_at (w v : Space3) :
    inner ℝ ((2 : ℝ) • (w - v)) v = ‖w‖ ^ 2 - ‖v‖ ^ 2 - ‖w - v‖ ^ 2 := by
  have hex : inner ℝ (w - v) (w - v) = ‖w‖ ^ 2 - 2 * inner ℝ w v + ‖v‖ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v w,
      real_inner_self_eq_norm_sq w, real_inner_self_eq_norm_sq v]
    ring
  have h2 : inner ℝ w v - inner ℝ v v = inner ℝ w v - ‖v‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq v]
  rw [real_inner_smul_left, inner_sub_left, h2]
  linarith [hex, real_inner_self_eq_norm_sq (w - v)]

/-- The bisector functional on the bisector direction. -/
theorem bisector_self (w v : Space3) :
    inner ℝ ((2 : ℝ) • (w - v)) (w - v) = 2 * ‖w - v‖ ^ 2 := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]

/-! ## Open Voronoi cells (pack1.hl:153-:322) -/

/-- HOL `voronoi_open` (pack1.hl:153; the `IN`-form of pack2.hl:25). -/
def voronoi_open (S : Set Space3) (v : Space3) : Set Space3 :=
  {x | ∀ w, w ∈ S → w ≠ v → dist x v < dist x w}

/-- HOL `bis` (pack1.hl:155). -/
def bis (u v : Space3) : Set Space3 := {x | dist x u = dist x v}

/-- HOL `nua_kg` (pack1.hl:157). -/
def nua_kg (u v : Space3) : Set Space3 := {x | dist x u < dist x v}

/-- HOL `saturated` (pack1.hl:159). -/
def saturated (S : Set Space3) : Prop := ∀ x : Space3, ∃ y ∈ S, dist x y < 2

/-- Squared-distance inequality in halfspace form (pack2's `BIS_LE`/`BIS_LT`
content, stated with `inner`; for `Space3` the dot `⬝ᵥ` is the real inner
product via `Kepler.Geom.inner_eq_dot`). -/
theorem sq_dist_le_iff (x u w : Space3) :
    ‖x - u‖ ^ 2 ≤ ‖x - w‖ ^ 2 ↔ 2 * inner ℝ (w - u) x ≤ ‖w‖ ^ 2 - ‖u‖ ^ 2 := by
  have ex : ∀ z : Space3, ‖x - z‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ z x + ‖z‖ ^ 2 := by
    intro z
    have h1 : ‖x - z‖ ^ 2 = inner ℝ (x - z) (x - z) := (real_inner_self_eq_norm_sq _).symm
    rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm x z,
      ← real_inner_self_eq_norm_sq x, ← real_inner_self_eq_norm_sq z]
    ring
  rw [ex u, ex w, inner_sub_left]
  constructor <;> intro h <;> linarith

theorem dist_le_dist_iff (x u w : Space3) :
    dist x u ≤ dist x w ↔ ((2 : ℝ) • (w - u)) ⬝ᵥ x ≤ ‖w‖ ^ 2 - ‖u‖ ^ 2 := by
  have hEq : ((2 : ℝ) • (w - u)) ⬝ᵥ x = 2 * inner ℝ (w - u) x := by
    rw [← inner_eq_dot, real_inner_smul_left]
  rw [hEq, dist_eq_norm, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← sq_dist_le_iff]


theorem sq_dist_lt_iff (x u w : Space3) :
    ‖x - u‖ ^ 2 < ‖x - w‖ ^ 2 ↔ 2 * inner ℝ (w - u) x < ‖w‖ ^ 2 - ‖u‖ ^ 2 := by
  constructor
  · intro h
    have hle := (sq_dist_le_iff x u w).mp (le_of_lt h)
    refine lt_of_le_of_ne hle fun hc => ?_
    have hneg : (u - w : Space3) = -(w - u) := by rw [neg_sub]
    have hrev := (sq_dist_le_iff x w u).mpr (le_of_eq (by
      rw [hneg, inner_neg_left]; linarith [hc]))
    exact lt_irrefl _ (lt_of_lt_of_le h hrev)
  · intro h
    have hle := (sq_dist_le_iff x u w).mpr (le_of_lt h)
    refine lt_of_le_of_ne hle fun hc => ?_
    have hge := (sq_dist_le_iff x w u).mp hc.symm.le
    have hsw : 2 * inner ℝ (u - w) x = -(2 * inner ℝ (w - u) x) := by
      rw [inner_sub_left, inner_sub_left]; ring
    have hR : ‖u‖ ^ 2 - ‖w‖ ^ 2 = -(‖w‖ ^ 2 - ‖u‖ ^ 2) := by ring
    rw [hsw, hR] at hge
    linarith


theorem dist_lt_dist_iff (x u w : Space3) :
    dist x u < dist x w ↔ ((2 : ℝ) • (w - u)) ⬝ᵥ x < ‖w‖ ^ 2 - ‖u‖ ^ 2 := by
  have hEq : ((2 : ℝ) • (w - u)) ⬝ᵥ x = 2 * inner ℝ (w - u) x := by
    rw [← inner_eq_dot, real_inner_smul_left]
  rw [hEq, dist_eq_norm, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← sq_dist_lt_iff]


/-- HOL `map_to_nua_kg` (pack1.hl:243). -/
def map_to_nua_kg (q : Space3 × Space3) : Set Space3 := nua_kg q.1 q.2

/-- HOL `voronoi_version2` (pack1.hl:161): the open cell is the intersection
of the halfspaces `nua_kg v y` over `y ∈ S ∖ {v}`. -/
theorem voronoi_version2 (v : Space3) (S : Set Space3) :
    voronoi_open S v = ⋂₀ (map_to_nua_kg '' ({v} ×ˢ (S \ {v}))) := by
  ext x
  constructor
  · intro hx s hs
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := hs
    rw [Set.mem_prod] at hq
    obtain ⟨ha, hbc⟩ := hq
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [Set.mem_sdiff] at hbc
    obtain ⟨hb, hb2⟩ := hbc
    exact hx b hb (fun hc => hb2 (by simp [hc]))
  · intro hx w hwS hwne
    exact hx (nua_kg v w) ⟨(v, w), ⟨rfl, hwS, hwne⟩, rfl⟩

/-- HOL `norm_ineq_lt` (pack1.hl:176). -/
theorem norm_ineq_lt (x y : Space3) : ‖x‖ < ‖y‖ ↔ x ⬝ᵥ x < y ⬝ᵥ y := by
  have e1 : x ⬝ᵥ x = ‖x‖ ^ 2 := by rw [← inner_eq_dot]; exact real_inner_self_eq_norm_sq x
  have e2 : y ⬝ᵥ y = ‖y‖ ^ 2 := by rw [← inner_eq_dot]; exact real_inner_self_eq_norm_sq y
  rw [e1, e2, sq_lt_sq₀ (norm_nonneg x) (norm_nonneg y)]

/-- Convexity of a strict inner-product halfspace (Mathlib's
`convex_halfSpace_lt`, in the `inner`-first-argument form). -/
theorem convex_halfspace_lt_of_inner (a : Space3) (b : ℝ) :
    Convex ℝ {x : Space3 | inner ℝ x a < b} := by
  have hlin : IsLinearMap ℝ (fun x : Space3 => inner ℝ a x) :=
    ⟨fun x y => by rw [inner_add_right], fun c x => by rw [real_inner_smul_right]; ring⟩
  have h := convex_halfSpace_lt hlin b
  rwa [show {w : Space3 | inner ℝ a w < b} = {x : Space3 | inner ℝ x a < b} from by
    ext x; simp only [Set.mem_setOf_eq, real_inner_comm]] at h

/-- Convexity of a closed inner-product halfspace. -/
theorem convex_halfspace_le_of_inner (a : Space3) (b : ℝ) :
    Convex ℝ {x : Space3 | inner ℝ x a ≤ b} := by
  have hlin : IsLinearMap ℝ (fun x : Space3 => inner ℝ a x) :=
    ⟨fun x y => by rw [inner_add_right], fun c x => by rw [real_inner_smul_right]; ring⟩
  have h := convex_halfSpace_le hlin b
  rwa [show {w : Space3 | inner ℝ a w ≤ b} = {x : Space3 | inner ℝ x a ≤ b} from by
    ext x; simp only [Set.mem_setOf_eq, real_inner_comm]] at h

/-- HOL `nua_kg_version2` (pack1.hl:179): a halfspace `nua_kg` is a strict
inner-product halfspace (HOL gives the coordinate form
`{x | x$1 * a$1 + x$2 * a$2 + x$3 * a$3 < b}`; here via `inner_eq_dot`). -/
theorem nua_kg_version2 (v y : Space3) :
    ∃ a : Space3, ∃ b : ℝ, nua_kg v y = {x : Space3 | inner ℝ x a < b} := by
  refine ⟨((2 : ℝ) • (y - v)), ‖y‖ ^ 2 - ‖v‖ ^ 2, ?_⟩
  ext x
  simp only [nua_kg, Set.mem_setOf_eq]
  rw [dist_lt_dist_iff x v y, ← inner_eq_dot,
    real_inner_comm ((2 : ℝ) • (y - v)) x]

/-- HOL `convex_nua_kg` (pack1.hl:191). -/
theorem convex_nua_kg (v y : Space3) : Convex ℝ (nua_kg v y) := by
  obtain ⟨a, b, hab⟩ := nua_kg_version2 v y
  rw [hab]
  exact convex_halfspace_lt_of_inner a b

/-- Convexity is closed under `⋂₀` (indexed-intersection form of
`convex_iInter`). -/
theorem convex_sInter {t : Set (Set Space3)} (h : ∀ s ∈ t, Convex ℝ s) :
    Convex ℝ (⋂₀ t) := by
  have hEq : (⋂₀ t : Set Space3) = ⋂ p : t, (p : Set Space3) := by
    ext x
    simp [Set.mem_iInter]
  rw [hEq]
  exact convex_iInter fun p => h p.1 p.2

/-- HOL `convex_voronoi` (pack1.hl:201). -/
theorem convex_voronoi (v : Space3) (S : Set Space3) : Convex ℝ (voronoi_open S v) := by
  rw [voronoi_version2]
  refine convex_sInter fun s hs => ?_
  obtain ⟨q, -, rfl⟩ := hs
  exact convex_nua_kg q.1 q.2

/-- HOL `bound_voronoi` (pack1.hl:209). -/
theorem bound_voronoi (v : Space3) (S : Set Space3) (hs : saturated S) :
    Bornology.IsBounded (voronoi_open S v) := by
  refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := v) (r := ‖v‖ + 2)) ?_
  intro x hx
  rw [Metric.mem_ball]
  obtain ⟨y, hyS, hxy⟩ := hs x
  rcases eq_or_ne y v with hyy | hyv
  · rw [hyy] at hxy
    linarith [norm_nonneg v, hxy]
  · calc dist x v ≤ dist x y := le_of_lt (hx y hyS hyv)
      _ < 2 := hxy
      _ ≤ ‖v‖ + 2 := by linarith [norm_nonneg v]

/-- HOL `surj_map_to_nua_kg` (pack1.hl:246). -/
theorem surj_map_to_nua_kg (v : Space3) (S : Set Space3) :
    map_to_nua_kg '' ({v} ×ˢ ((S \ {v}) ∩ Metric.ball v 4)) =
      {q : Set Space3 | ∃ y : Space3, y ∈ S \ {v} ∧ y ∈ Metric.ball v 4 ∧ q = nua_kg v y} := by
  ext q
  constructor
  · rintro ⟨⟨a, b⟩, hq, rfl⟩
    rw [Set.mem_prod] at hq
    obtain ⟨ha, hbc⟩ := hq
    have ha' : a = v := Set.mem_singleton_iff.mp ha
    rw [ha'] at hbc ⊢
    rw [Set.mem_inter_iff] at hbc
    obtain ⟨hsd, hball⟩ := hbc
    rw [Set.mem_sdiff] at hsd
    obtain ⟨hb, hb2⟩ := hsd
    exact ⟨b, ⟨hb, hb2⟩, hball, rfl⟩
  · rintro ⟨y, hy, hyball, rfl⟩
    exact ⟨(v, y), ⟨rfl, hy, hyball⟩, rfl⟩

/-- HOL `finite_voronoi2` (pack1.hl:254). -/
theorem finite_voronoi2 (v : Space3) (S : Set Space3) (hV : Packing S) :
    {q : Set Space3 |
      ∃ y : Space3, y ∈ S \ {v} ∧ y ∈ Metric.ball v 4 ∧ q = nua_kg v y}.Finite := by
  have hEq : {q : Set Space3 |
      ∃ y : Space3, y ∈ S \ {v} ∧ y ∈ Metric.ball v 4 ∧ q = nua_kg v y} =
      nua_kg v '' ((S ∩ Metric.ball v 4) \ {v}) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_sdiff,
      Set.mem_singleton_iff]
    tauto
  rw [hEq]
  exact ((KIUMVTC' v 4 S hV).sdiff).image (nua_kg v)

/-- HOL `real_sub_norm` (pack1.hl:261). -/
theorem real_sub_norm (x y z : Space3) : dist x z - dist y z ≤ dist x y := by
  linarith [dist_triangle x y z]

/-- HOL `not_open` (pack1.hl:265): a sequential characterization of
non-openness. -/
theorem not_open {s : Set Space3} :
    ¬ IsOpen s ↔ ∃ a : Space3, ∃ x : ℕ → Space3, a ∈ s ∧ (∀ n, x n ∉ s) ∧
      Tendsto x atTop (𝓝 a) := by
  classical
  constructor
  · intro h
    rw [Metric.isOpen_iff] at h
    push_neg at h
    obtain ⟨a, ha, hballs⟩ := h
    have hex : ∀ n : ℕ, ∃ z, z ∈ Metric.ball a (1 / (n + 1)) ∧ z ∉ s := fun n =>
      not_subset.mp (hballs (1 / (n + 1)) (by positivity))
    choose! f hf1 hf2 using hex
    refine ⟨a, f, ha, hf2, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨Nat.ceil (1 / ε), fun n hn => ?_⟩
    have h1 : (1 : ℝ) / ε ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h4 : (1 : ℝ) ≤ ε * n := by linarith [(div_le_iff₀ hε).mp h1]
    have h3 : (1 : ℝ) / (n + 1) < ε := by
      rw [div_lt_iff₀ (by nlinarith : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith
    exact lt_trans (Metric.mem_ball.mp (hf1 n)) h3
  · rintro ⟨a, x, ha, hx, hxa⟩ hopen
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a ha
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hxa ε hε
    exact hx N (hball (Metric.mem_ball.mpr (hN N (Nat.le_refl _))))

/-- HOL `not_open_voronoi1` (pack1.hl:270): a sequential-compactness
pigeonhole for finitely many centers. Straggler (`sorry`): the extraction of
a convergent subsequence along an infinite fiber needs extra scaffolding in
Mathlib. -/
theorem not_open_voronoi1 (x : ℕ → Space3) (y : ℕ → Space3) (v : Space3) (w : Space3)
    (A : Set Space3) (hA : A.Finite) (hxa : Tendsto x atTop (𝓝 w))
    (hxy : ∀ n, dist (x n) v ≥ dist (x n) (y n))
    (hyA : ¬ ∃ N : ℕ, ∀ n, N < n → y n ∉ A) :
    ∃ a, a ∈ A ∧ dist w v ≥ dist w a := by
  sorry

/-- HOL `not_open_voronoi2` (pack1.hl:274). -/
theorem not_open_voronoi2 (x : ℕ → Space3) (v w : Space3) (hx : Tendsto x atTop (𝓝 w))
    (hN : ∃ N : ℕ, ∀ n : ℕ, N < n → (2 : ℝ) ≤ dist (x n) v) : (2 : ℝ) ≤ dist w v := by
  obtain ⟨N, hN⟩ := hN
  have hA : IsClosed {y : Space3 | (2 : ℝ) ≤ dist y v} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hmem : w ∈ closure {y : Space3 | (2 : ℝ) ≤ dist y v} :=
    mem_closure_of_tendsto hx
      (Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => hN n (by linarith)⟩)
  rwa [hA.closure_eq] at hmem

/-- HOL `not_in_voronoi` (pack1.hl:277). -/
theorem not_in_voronoi (x v : Space3) (S : Set Space3) :
    x ∉ voronoi_open S v ↔ ∃ y, y ∈ S ∧ y ≠ v ∧ dist x y ≤ dist x v := by
  simp only [voronoi_open, Set.mem_setOf_eq]
  push_neg
  exact Iff.rfl

/-- HOL `not_open_voronoi3` (pack1.hl:280). -/
theorem not_open_voronoi3 (v : Space3) (S : Set Space3) (h : ¬ IsOpen (voronoi_open S v)) :
    ∃ x : ℕ → Space3, ∃ a : Space3, ∃ y : ℕ → Space3,
      a ∈ voronoi_open S v ∧ (∀ n, x n ∉ voronoi_open S v) ∧ Tendsto x atTop (𝓝 a) ∧
        (∀ n, y n ∈ S ∧ y n ≠ v ∧ dist (x n) (y n) ≤ dist (x n) v) := by
  classical
  obtain ⟨a, x, ha, hx, hxa⟩ := not_open.mp h
  by_cases hcase : ∃ y : ℕ → Space3, ∀ n, y n ∈ S ∧ y n ≠ v ∧ dist (x n) (y n) ≤ dist (x n) v
  · exact ⟨x, a, hcase.choose, ha, hx, hxa, hcase.choose_spec⟩
  · exfalso
    have hcase' : ∀ y : ℕ → Space3, ∃ n,
        ¬(y n ∈ S ∧ y n ≠ v ∧ dist (x n) (y n) ≤ dist (x n) v) := fun y =>
      not_forall.mp fun hall => hcase ⟨y, hall⟩
    have hex : ∀ n : ℕ, ∃ z : Space3, z ∈ S ∧ z ≠ v ∧ dist (x n) z ≤ dist (x n) v := by
      intro n
      by_contra hc
      exact hx n (not_not.mp (((not_in_voronoi (x n) v S).not).mpr hc))
    choose g hg1 hg2 hg3 using hex
    obtain ⟨n, hn⟩ := hcase' g
    exact hn ⟨hg1 n, hg2 n, hg3 n⟩

/-- HOL `voronoi_in_ball` (pack1.hl:285). -/
theorem voronoi_in_ball (x v : Space3) (S : Set Space3) (hV : Packing S) (hs : saturated S)
    (hx : x ∈ voronoi_open S v) : dist x v < 2 := by
  obtain ⟨y, hyS, hxy⟩ := hs x
  rcases eq_or_ne y v with rfl | hyv
  · exact hxy
  · linarith [hx y hyS hyv]

/-- HOL `open_voronoi` (pack1.hl:297), proved directly by a uniform-gap
argument over the finitely many centers within distance 4 (HL detours
through `not_open_voronoi1`-`3`). -/
theorem open_voronoi (v : Space3) (S : Set Space3) (hV : Packing S) (hs : saturated S) :
    IsOpen (voronoi_open S v) := by
  classical
  rw [Metric.isOpen_iff]
  rintro x₀ hx₀
  have hD : dist x₀ v < 2 := voronoi_in_ball x₀ v S hV hs hx₀
  set F : Set Space3 := (S ∩ Metric.ball v 4) \ {v} with hFdef
  have hFfin : F.Finite := (KIUMVTC' v 4 S hV).sdiff
  have hpos : ∀ w ∈ F, 0 < dist x₀ w - dist x₀ v := by
    intro w hw
    obtain ⟨⟨hwS, -⟩, hwv⟩ := hw
    have hwne : w ≠ v := by simpa using hwv
    linarith [hx₀ w hwS hwne]
  have hmin : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ F, dist x₀ v + m ≤ dist x₀ w := by
    by_cases hFe : F = ∅
    · refine ⟨1, one_pos, ?_⟩
      intro w hw
      exact absurd hw (by rw [hFe]; simp)
    · have hne : hFfin.toFinset.Nonempty := by
        obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hFe
        exact ⟨w, hFfin.mem_toFinset.mpr hw⟩
      have htne : (hFfin.toFinset.image (fun w => dist x₀ w - dist x₀ v)).Nonempty := by
        obtain ⟨w, hw⟩ := hne
        exact ⟨dist x₀ w - dist x₀ v, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
      refine ⟨(hFfin.toFinset.image (fun w => dist x₀ w - dist x₀ v)).min' htne, ?_, ?_⟩
      · rcases Finset.mem_image.mp (Finset.min'_mem _ htne) with ⟨w₀, hw₀, hw₀eq⟩
        rw [← hw₀eq]
        exact hpos w₀ (hFfin.mem_toFinset.mp hw₀)
      · intro w hw
        have hwT : w ∈ hFfin.toFinset := hFfin.mem_toFinset.mpr hw
        have himg : (fun w : Space3 => dist x₀ w - dist x₀ v) w ∈
            hFfin.toFinset.image (fun w : Space3 => dist x₀ w - dist x₀ v) :=
          Finset.mem_image.mpr ⟨w, hwT, rfl⟩
        have hle := Finset.min'_le _ _ himg
        linarith
  obtain ⟨m, hmpos, hmle⟩ := hmin
  refine ⟨min (m / 3) ((2 - dist x₀ v) / 3), lt_min (by linarith) (by linarith), ?_⟩
  intro y hy
  rw [Metric.mem_ball] at hy
  have hy1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 := lt_of_lt_of_le hy (min_le_right _ _)
  intro w hwS hwv
  by_cases hwF : w ∈ F
  · have hwb : dist w v < 4 := by
      have h5 := hwF.1.2
      rw [Metric.mem_ball] at h5
      exact h5
    have h1 : dist x₀ w ≤ dist x₀ y + dist y w := dist_triangle x₀ y w
    have h2 := hmle w hwF
    have h3 : dist y v ≤ dist y x₀ + dist x₀ v := dist_triangle y x₀ v
    linarith [hy1, hy2, h1, h2, h3, dist_comm x₀ y]
  · have hw4 : (4 : ℝ) ≤ dist v w := by
      by_contra hc
      exact hwF ⟨⟨hwS, by rw [Metric.mem_ball]; linarith [lt_of_not_ge hc, dist_comm v w]⟩,
        by simpa using hwv⟩
    have h1 : dist v w ≤ dist v y + dist y w := dist_triangle v y w
    have h2 : dist y v ≤ dist y x₀ + dist x₀ v := dist_triangle y x₀ v
    have h3 : dist v y = dist y v := dist_comm v y
    linarith [hy1, hy2]

/-- HOL `DRUQUFE` (pack1.hl:315), open-cell form. -/
theorem DRUQUFE (v : Space3) (S : Set Space3) (hV : Packing S) (hs : saturated S) :
    Convex ℝ (voronoi_open S v) ∧ Bornology.IsBounded (voronoi_open S v) ∧
      IsOpen (voronoi_open S v) ∧ MeasurableSet (voronoi_open S v) :=
  ⟨convex_voronoi v S, bound_voronoi v S hs, open_voronoi v S hV hs,
    (open_voronoi v S hV hs).measurableSet⟩

/-- HOL `measurable_voronoi` (pack1.hl:322). -/
theorem measurable_voronoi (v : Space3) (S : Set Space3) (hV : Packing S) (hs : saturated S) :
    MeasurableSet (voronoi_open S v) :=
  (open_voronoi v S hV hs).measurableSet

/-! ## The density chain on open cells (pack1.hl:329-:597) -/

/-- HOL `negligible_fun_p` (pack1.hl:329). HOL sums over the set
`S ∩ ball(p, r)`; encoded as a `Finset` sum over its `toFinset` (finite for
packings by `KIUMVTC`). -/
def negligible_fun_p (f : Space3 → ℝ) (S : Set Space3) (p : Space3) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ h : (S ∩ Metric.ball p r).Finite,
    (∑ v ∈ h.toFinset, f v) ≤ C * r ^ 2

/-- HOL `fcc_compatible` (pack1.hl:332), open-cell form. -/
def fcc_compatible (f : Space3 → ℝ) (S : Set Space3) : Prop :=
  ∀ v ∈ S, Real.sqrt 32 ≤ (volume (voronoi_open S v)).toReal + f v

/-- HOL `packing_subset_unions_ball` (pack1.hl:335). -/
theorem packing_subset_unions_ball (S : Set Space3) (p : Space3) (r : ℝ) :
    ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r) ⊆
      ⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1 := by
  sorry


/-- HOL `measurable_packing_lm1` (pack1.hl:339). -/
theorem measurable_packing_lm1 (S : Set Space3) (p : Space3) (r : ℝ) :
    MeasurableSet ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r) :=
  ((isOpen_iUnion fun v => isOpen_iUnion fun (_ : v ∈ S) => isOpen_ball).inter
    isOpen_ball).measurableSet

/-- Rewrite of a finite-set-indexed union as a `Finset`-indexed union. -/
theorem biUnion_toFinset_eq {α ι : Type*} [DecidableEq ι] {t : Set ι} (ht : t.Finite)
    (f : ι → Set α) : (⋃ i ∈ t, f i) = ⋃ i ∈ ht.toFinset, f i := by
  ext x
  simp

/-- HOL `measurable_packing_lm2` (pack1.hl:353). -/
theorem measurable_packing_lm2 (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    MeasurableSet (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1) := by
  sorry


/-- The volume of a ball in `Space3` is finite. -/
theorem volume_ball_ne_top (c : Space3) (q : ℝ) : volume (Metric.ball c q) ≠ ⊤ := by
  intro hq
  rw [EuclideanSpace.volume_ball_fin_three] at hq
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top hq

/-- The volume of a unit ball in `Space3`. -/
theorem volume_ball_one (c : Space3) : (volume (Metric.ball c 1)).toReal = 4 * Real.pi / 3 := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- HOL `measure_ineq_lm53_1` (pack1.hl:357). -/
theorem measure_ineq_lm53_1 (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal ≤
      (volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1)).toReal := by
  classical
  have hsub := packing_subset_unions_ball S p r
  have hsub2 : (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1) ⊆ Metric.ball p (r + 3) := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    rw [Metric.mem_ball] at hxv ⊢
    have h1 : dist p x ≤ dist p v + dist x v := by
      linarith [dist_triangle p v x, dist_comm v x]
    linarith [Metric.mem_ball.mp hv.2, hxv, dist_comm x p, dist_comm v p]
  have hL : volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r) ≠ ⊤ :=
    fun hc => volume_ball_ne_top p (r + 3)
      (top_le_iff.mp (le_trans (le_trans (le_of_eq hc.symm) (measure_mono hsub))
        (measure_mono hsub2)))
  have hR : volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1) ≠ ⊤ :=
    fun hc => volume_ball_ne_top p (r + 3)
      (top_le_iff.mp (le_trans (le_of_eq hc.symm) (measure_mono hsub2)))
  exact (ENNReal.toReal_le_toReal hL hR).mpr (measure_mono hsub)


/-- HOL `card_eq_ball_point` (pack1.hl:371). -/
theorem card_eq_ball_point (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    ({q : Set Space3 | ∃ x ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball x 1}).ncard =
      (S ∩ Metric.ball p (r + 1)).ncard := by
  classical
  have hinj : Set.InjOn (fun x : Space3 => Metric.ball x 1)
      (S ∩ Metric.ball p (r + 1)) := by
    intro x hx y hy hxy
    have hxy' : Metric.ball x 1 = Metric.ball y 1 := hxy
    by_contra hne
    have h1 : x ∈ Metric.ball y 1 := by
      have hx1 : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
      rwa [hxy'] at hx1
    have h2 : y ∈ Metric.ball x 1 := by
      have hy1 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
      rw [← hxy'] at hy1
      exact hy1
    rw [Metric.mem_ball] at h1 h2
    have h3 : 2 ≤ dist x y := (packing_iff_ne S).mp hV x y hx.1 hy.1 hne
    linarith [dist_comm x y]
  have hEq : {q : Set Space3 | ∃ x ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball x 1} =
      (fun x : Space3 => Metric.ball x 1) '' (S ∩ Metric.ball p (r + 1)) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_image]
    tauto
  rw [hEq, Set.InjOn.ncard_image hinj]

/-- HOL `measure_ineq_lm53_2` (pack1.hl:363). Straggler (`sorry`): the
`ℝ≥0∞`-to-`ℝ` volume bookkeeping for the union of unit balls. -/
theorem measure_ineq_lm53_2 (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal ≤
      (({q : Set Space3 |
        ∃ v ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball v 1}).ncard : ℝ) *
        4 * Real.pi / 3 := by
  sorry

/-- HOL `voronoi_subset_ball` (pack1.hl:380). -/
theorem voronoi_subset_ball (v : Space3) (S : Set Space3) (hV : Packing S)
    (hs : saturated S) : voronoi_open S v ⊆ Metric.ball v 2 := by
  intro x hx
  rw [Metric.mem_ball]
  exact voronoi_in_ball x v S hV hs hx

/-- HOL `all_voronoi_subset_ball` (pack1.hl:383). -/
theorem all_voronoi_subset_ball (v : Space3) (S : Set Space3) (p : Space3) (r : ℝ)
    (hV : Packing S) (hs : saturated S) (hv : v ∈ Metric.ball p (r + 1)) :
    voronoi_open S v ⊆ Metric.ball p (r + 3) := by
  intro x hx
  rw [Metric.mem_ball] at hv ⊢
  have h1 : dist p x ≤ dist p v + dist x v := by
    linarith [dist_triangle p v x, dist_comm v x]
  have h2 : dist x v < 2 := voronoi_in_ball x v S hV hs hx
  linarith [Metric.mem_ball.mp hv, h1, h2, dist_comm x p, dist_comm v p]

/-- HOL `unions_voronoi_center_in_ball_subset_ball` (pack1.hl:385). -/
theorem unions_voronoi_center_in_ball_subset_ball (S : Set Space3) (p : Space3) (r : ℝ)
    (hV : Packing S) (hs : saturated S) :
    (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), voronoi_open S v) ⊆ Metric.ball p (r + 3) := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
  exact all_voronoi_subset_ball v S p r hV hs hv.2 hxv

/-- HOL `map_to_voronoi` (pack1.hl:388). -/
def map_to_voronoi (q : Space3 × Set Space3) : Set Space3 := voronoi_open q.2 q.1

/-- HOL `surj_map_to_voronoi_db` (pack1.hl:390). -/
theorem surj_map_to_voronoi_db (S : Set Space3) (p : Space3) (r : ℝ) :
    map_to_voronoi '' ((S ∩ Metric.ball p (r + 1)) ×ˢ {S}) =
      {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
        v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = voronoi_open w v} := by
  sorry


/-- HOL `finite_set_voronoi_center_in_ball` (pack1.hl:394). -/
theorem finite_set_voronoi_center_in_ball (S : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing S) :
    {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
      v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = voronoi_open w v}.Finite := by
  sorry


/-- HOL `measurable_unions_voronoi` (pack1.hl:398). -/
theorem measurable_unions_voronoi (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) (hs : saturated S) :
    MeasurableSet (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), voronoi_open S v) := by
  sorry


/-- HOL `negligible_voronoi` (pack1.hl:400): distinct open cells are
disjoint, hence null. -/
theorem negligible_voronoi (S : Set Space3) (p : Space3) (r : ℝ) :
    ∀ s ∈ {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
        v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = voronoi_open w v},
      ∀ t ∈ {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
        v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = voronoi_open w v},
        s ≠ t → volume (s ∩ t) = 0 := by
  sorry


/-- HOL `inj_map_to_voronoi` (pack1.hl:407). -/
theorem inj_map_to_voronoi (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    ∀ q1 ∈ ((S ∩ Metric.ball p (r + 1)) ×ˢ {S}),
      ∀ q2 ∈ ((S ∩ Metric.ball p (r + 1)) ×ˢ {S}),
        map_to_voronoi q1 = map_to_voronoi q2 → q1 = q2 := by
  sorry


/-- HOL `measure_unions_sum_voronoi` (pack1.hl:417), open-cell form. -/
theorem measure_unions_sum_voronoi (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) (hs : saturated S) (hfin : (S ∩ Metric.ball p (r + 1)).Finite) :
    (volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), voronoi_open S v)).toReal =
      ∑ v ∈ hfin.toFinset, (volume (voronoi_open S v)).toReal := by
  sorry



/-- HOL `sum_measure_voronoi_le_ball` (pack1.hl:470), open-cell form. -/
theorem sum_measure_voronoi_le_ball (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) (hs : saturated S) (hfin : (S ∩ Metric.ball p (r + 1)).Finite) :
    ∑ v ∈ hfin.toFinset, (volume (voronoi_open S v)).toReal ≤
      (volume (Metric.ball p (r + 3))).toReal := by
  sorry



/-- HOL `ineq_lm5_3_step3` (pack1.hl:476), open-cell form. -/
theorem ineq_lm5_3_step3 (S : Set Space3) (p : Space3) (r : ℝ) (A : Space3 → ℝ)
    (hr : 0 ≤ r) (hV : Packing S) (hs : saturated S) (hfcc : fcc_compatible A S)
    (hfin : (S ∩ Metric.ball p (r + 1)).Finite) :
    Real.sqrt 32 * ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) ≤
      ∑ v ∈ hfin.toFinset, (A v + (volume (voronoi_open S v)).toReal) := by
  have h1 : ∑ v ∈ hfin.toFinset, Real.sqrt 32 ≤
      ∑ v ∈ hfin.toFinset, (A v + (volume (voronoi_open S v)).toReal) := by
    refine Finset.sum_le_sum fun v hv => ?_
    have hvT : v ∈ (S ∩ Metric.ball p (r + 1)) := hfin.mem_toFinset.mp hv
    have hh := hfcc v hvT.1
    linarith
  have h2 : Real.sqrt 32 * ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) =
      ∑ v ∈ hfin.toFinset, Real.sqrt 32 := by
    rw [Set.ncard_eq_toFinset_card (S ∩ Metric.ball p (r + 1)) hfin, Finset.sum_const,
      nsmul_eq_mul]
    exact mul_comm _ _
  rw [h2]
  exact h1



/-- HOL `ineq_lm5_3_step4` (pack1.hl:485): for every `c ≥ 0` there is a
constant `c'` (here `63π/√18 + 4c/√32`) making the density bound absorb the
`(1 + 3/r)³` and packing-count error terms. -/
theorem ineq_lm5_3_step4 (c : ℝ) (hc : 0 ≤ c) :
    ∃ c' : ℝ, ∀ r : ℝ, 1 ≤ r →
      Real.pi / Real.sqrt 18 * (1 + 3 / r) ^ 3 +
          c * (r + 1) ^ 2 / (r ^ 3 * Real.sqrt 32) ≤
        Real.pi / Real.sqrt 18 + c' / r := by
  sorry


/-- HOL `JGXZYGW` (pack1.hl:519), the density bound conditional on an
`fcc_compatible` and `negligible_fun_p` functional. Straggler (`sorry`):
depends on `measure_ineq_lm53_2`. -/
theorem JGXZYGW (S : Set Space3) (p : Space3) (hV : Packing S) (hs : saturated S) :
    (∃ A : Space3 → ℝ, fcc_compatible A S ∧ negligible_fun_p A S p) →
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal /
        (volume (Metric.ball p r)).toReal ≤
        Real.pi / Real.sqrt 18 + c / r := by
  sorry

/-! ## Closed Voronoi cells (pack2.hl) -/

/-- HOL `voronoi_closed` (pack2.hl:30), renamed `voronoi`: the closed cell
of `v` with respect to `S`. -/
def voronoi (S : Set Space3) (v : Space3) : Set Space3 :=
  {x | ∀ w, w ∈ S → dist x v ≤ dist x w}

/-- HOL `bis_le` (pack2.hl:49). -/
def bis_le (u v : Space3) : Set Space3 :=
  {x | ((2 : ℝ) • (v - u)) ⬝ᵥ x ≤ ‖v‖ ^ 2 - ‖u‖ ^ 2}

/-- HOL `bis_lt` (pack2.hl:56). -/
def bis_lt (u v : Space3) : Set Space3 :=
  {x | ((2 : ℝ) • (v - u)) ⬝ᵥ x < ‖v‖ ^ 2 - ‖u‖ ^ 2}

/-- HOL `VORONOI_OPEN` (pack2.hl:25), trivial in this encoding. -/
theorem VORONOI_OPEN (s : Set Space3) (v : Space3) :
    voronoi_open s v = {x | ∀ w, w ∈ s → w ≠ v → dist x v < dist x w} := rfl

/-- HOL `VORONOI_CLOSED` (pack2.hl:30), trivial in this encoding. -/
theorem VORONOI_CLOSED (s : Set Space3) (v : Space3) :
    voronoi s v = {x | ∀ w, w ∈ s → dist x v ≤ dist x w} := rfl

/-- HOL `VORONOI_CLOSED_ALT` (pack2.hl:63). -/
theorem VORONOI_CLOSED_ALT (s : Set Space3) (v : Space3) :
    voronoi s v = {x | ∀ w, w ∈ s → w ≠ v → dist x v ≤ dist x w} := by
  ext x
  simp only [voronoi, Set.mem_setOf_eq]
  constructor
  · intro h w hw _
    exact h w hw
  · intro h w hw
    rcases eq_or_ne w v with rfl | hne
    · exact le_refl _
    · exact h w hw hne

/-- HOL `BIS_LE` (pack2.hl:49) as a set equality with the halfspace
`dist`-form. -/
theorem BIS_LE (u v : Space3) :
    bis_le u v = {x | dist x u ≤ dist x v} := by
  ext x
  simp only [bis_le, Set.mem_setOf_eq]
  rw [dist_le_dist_iff x u v]

/-- HOL `BIS_LT` (pack2.hl:56). -/
theorem BIS_LT (u v : Space3) :
    bis_lt u v = {x | dist x u < dist x v} := by
  ext x
  simp only [bis_lt, Set.mem_setOf_eq]
  rw [dist_lt_dist_iff x u v]

/-- HOL `VORONOI_CLOSED_AS_INTERSECTION` (pack2.hl:69). -/
theorem VORONOI_CLOSED_AS_INTERSECTION (s : Set Space3) (v : Space3) :
    voronoi s v = ⋂₀ (bis_le v '' (s \ {v})) := by
  ext x
  rw [voronoi, Set.mem_setOf_eq, Set.mem_sInter]
  constructor
  · intro h t ht
    obtain ⟨w, hw, rfl⟩ := ht
    exact (dist_le_dist_iff x v w).mp (h w hw.1)
  · intro h w hw
    rcases eq_or_ne w v with rfl | hwne
    · exact le_refl _
    · refine (dist_le_dist_iff x v w).symm.mp ?_
      exact h (bis_le v w) ⟨w, Set.mem_sdiff_of_mem hw (by simpa using hwne), rfl⟩

/-- HOL `VORONOI_OPEN_AS_INTERSECTION` (pack2.hl:74). -/
theorem VORONOI_OPEN_AS_INTERSECTION (s : Set Space3) (v : Space3) :
    voronoi_open s v = ⋂₀ (bis_lt v '' (s \ {v})) := by
  ext x
  rw [voronoi_open, Set.mem_setOf_eq, Set.mem_sInter]
  constructor
  · intro h t ht
    obtain ⟨w, hw, rfl⟩ := ht
    exact (dist_lt_dist_iff x v w).mp (h w hw.1 hw.2)
  · intro h w hw hwne
    refine (dist_lt_dist_iff x v w).symm.mp ?_
    exact h (bis_lt v w) ⟨w, Set.mem_sdiff_of_mem hw (by simpa using hwne), rfl⟩

/-- HOL `CLOSED_BIS_LE` (pack2.hl:280). -/
theorem CLOSED_BIS_LE (u v : Space3) : IsClosed (bis_le u v) := by
  have hcont : Continuous (fun x : Space3 => inner ℝ (((2 : ℝ) • (v - u))) x) :=
    continuous_const.inner continuous_id
  have hEq : bis_le u v = {x : Space3 | inner ℝ (((2 : ℝ) • (v - u))) x ≤ ‖v‖ ^ 2 - ‖u‖ ^ 2} := by
    ext x
    simp only [bis_le, Set.mem_setOf_eq, ← inner_eq_dot]
  rw [hEq]
  exact isClosed_le hcont continuous_const

/-- Closed halfspace convexity, `bis_le`-shaped. -/
theorem convex_bis_le (u v : Space3) : Convex ℝ (bis_le u v) := by
  have hEq : bis_le u v =
      {x : Space3 | inner ℝ x ((2 : ℝ) • (v - u)) ≤ ‖v‖ ^ 2 - ‖u‖ ^ 2} := by
    ext x
    simp only [bis_le, Set.mem_setOf_eq, ← inner_eq_dot, real_inner_comm]
  rw [hEq]
  exact convex_halfspace_le_of_inner _ _


/-- HOL `CLOSED_VORONOI_CLOSED` (pack2.hl:79). -/
theorem CLOSED_VORONOI_CLOSED (s : Set Space3) (v : Space3) : IsClosed (voronoi s v) := by
  rw [VORONOI_CLOSED_AS_INTERSECTION]
  exact isClosed_sInter fun y hy => by
    obtain ⟨w, -, rfl⟩ := hy
    exact CLOSED_BIS_LE v w

/-- HOL `CONVEX_VORONOI_CLOSED` (pack2.hl:105). -/
theorem CONVEX_VORONOI_CLOSED (s : Set Space3) (v : Space3) : Convex ℝ (voronoi s v) := by
  rw [VORONOI_CLOSED_AS_INTERSECTION]
  exact convex_sInter fun y hy => by
    obtain ⟨w, -, rfl⟩ := hy
    exact convex_bis_le v w

/-- HOL `VORONOI_CLOSED_SUBSET_BALL` (pack2.hl:85). -/
theorem VORONOI_CLOSED_SUBSET_BALL (s : Set Space3) (v : Space3) (hs : saturated s) :
    voronoi s v ⊆ Metric.ball v 2 := by
  intro x hx
  rw [Metric.mem_ball]
  obtain ⟨y, hyS, hxy⟩ := hs x
  rcases eq_or_ne y v with rfl | hyv
  · exact hxy
  · linarith [hx y hyS]

/-- HOL `BOUNDED_VORONOI_CLOSED` (pack2.hl:96). -/
theorem BOUNDED_VORONOI_CLOSED (s : Set Space3) (v : Space3) (hs : saturated s) :
    Bornology.IsBounded (voronoi s v) :=
  Bornology.IsBounded.subset (Metric.isBounded_ball (x := v) (r := 2)) (VORONOI_CLOSED_SUBSET_BALL s v hs)

/-- HOL `COMPACT_VORONOI_CLOSED` (pack2.hl:100). -/
theorem COMPACT_VORONOI_CLOSED (s : Set Space3) (v : Space3) (hs : saturated s) :
    IsCompact (voronoi s v) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨CLOSED_VORONOI_CLOSED s v, BOUNDED_VORONOI_CLOSED s v hs⟩

/-- HOL `BASE_IN_VORONOI_CLOSED` (pack2.hl:111). -/
theorem BASE_IN_VORONOI_CLOSED (s : Set Space3) (v : Space3) : v ∈ voronoi s v := by
  intro w _
  rw [dist_self]
  exact dist_nonneg

/-- HOL `PACKING_IMP_CLOSED` (pack2.hl:124). -/
theorem PACKING_IMP_CLOSED (s : Set Space3) (h : Packing s) : IsClosed s := by
  have hc : ∀ x ∈ closure s, x ∈ s := by
    intro x hx
    by_contra hxS
    obtain ⟨y₀, hy₀S, hy₀d⟩ := Metric.mem_closure_iff.mp hx (1 / 2) (by norm_num)
    have h1 : dist x y₀ ≠ 0 := by
      intro h0
      have hxy : x = y₀ := dist_eq_zero.mp h0
      exact hxS (by rw [hxy]; exact hy₀S)
    obtain ⟨y₁, hy₁S, hy₁d⟩ := Metric.mem_closure_iff.mp hx (dist x y₀) (by positivity)
    have hy₁ne : y₁ ≠ y₀ := by
      intro hcc
      rw [hcc] at hy₁d
      exact lt_irrefl _ hy₁d
    have h3 : 2 ≤ dist y₀ y₁ := (packing_iff_ne s).mp h y₀ y₁ hy₀S hy₁S hy₁ne.symm
    have h4 : dist y₀ y₁ ≤ dist y₀ x + dist x y₁ := dist_triangle y₀ x y₁
    have h5 : dist y₀ x = dist x y₀ := dist_comm y₀ x
    linarith
  refine ⟨?_⟩
  rw [Metric.isOpen_iff]
  intro x hx
  have hxc : x ∉ closure s := fun hcc => hx (hc x hcc)
  rw [Metric.mem_closure_iff] at hxc
  push_neg at hxc
  obtain ⟨ε, hε, hball⟩ := hxc
  refine ⟨ε, hε, fun y hy => ?_⟩
  rw [Metric.mem_ball] at hy
  by_contra hyS
  have hyS' : y ∈ s := by
    rw [Set.mem_compl_iff] at hyS
    exact not_not.mp hyS
  exact absurd (Metric.mem_ball.mp hy) (not_lt.mpr (by rw [dist_comm]; exact hball y hyS'))


/-- HOL `SATURATED_IMP_NONEMPTY` (pack2.hl:130). -/
theorem SATURATED_IMP_NONEMPTY (s : Set Space3) (h : saturated s) : s.Nonempty := by
  obtain ⟨y, hyS, -⟩ := h 0
  exact ⟨y, hyS⟩

/-- HOL `VORONOI_CLOSED_PARTITION_STRONG` (pack2.hl:115). Straggler
(`sorry`): needs the existence of a nearest point in a closed nonempty set
(HOL's `CLOSEST_POINT_EXISTS`). -/
theorem VORONOI_CLOSED_PARTITION_STRONG (s : Set Space3) (hS : IsClosed s) (hne : s ≠ ∅) :
    (⋃ v ∈ s, voronoi s v) = Set.univ := by
  sorry

/-- HOL `VORONOI_CLOSED_PARTITION` (pack2.hl:134). Blocked by
`VORONOI_CLOSED_PARTITION_STRONG`. -/
theorem VORONOI_CLOSED_PARTITION (s : Set Space3) (hV : Packing s) (hs : saturated s) :
    (⋃ v ∈ s, voronoi s v) = Set.univ := by
  sorry

/-- HOL `VORONOI_CLOSED_AS_FINITE_INTERSECTION` (pack2.hl:140). Straggler
(`sorry`): the proof uses `HALFLINE_INTER_COMPACT_SEGMENT` (intersection of a
ray with a compact convex cell is a segment), which has no Mathlib
counterpart here. -/
theorem VORONOI_CLOSED_AS_FINITE_INTERSECTION (s : Set Space3) (v : Space3)
    (hV : Packing s) (hs : saturated s) (hv : v ∈ s) :
    voronoi s v = ⋂₀ (bis_le v '' ((s ∩ Metric.ball v 4) \ {v})) := by
  sorry

/-- HOL `POLYHEDRON_VORONOI_CLOSED` (pack2.hl:256). Blocked by
`VORONOI_CLOSED_AS_FINITE_INTERSECTION`. -/
theorem POLYHEDRON_VORONOI_CLOSED (s : Set Space3) (v : Space3) (hV : Packing s)
    (hs : saturated s) (hv : v ∈ s) : polyhedron (voronoi s v) := by
  sorry

/-- HOL `POLYTOPE_VORONOI_CLOSED` (pack2.hl:266). Blocked by
`VORONOI_CLOSED_AS_FINITE_INTERSECTION` (boundedness comes from
`BOUNDED_VORONOI_CLOSED`). -/
theorem POLYTOPE_VORONOI_CLOSED (s : Set Space3) (v : Space3) (hV : Packing s)
    (hs : saturated s) (hv : v ∈ s) : polytope (voronoi s v) := by
  sorry

/-- HOL `MEASURABLE_VORONOI_CLOSED` (pack2.hl:272). -/
theorem MEASURABLE_VORONOI_CLOSED (s : Set Space3) (v : Space3) (hs : saturated s) :
    MeasurableSet (voronoi s v) :=
  (COMPACT_VORONOI_CLOSED s v hs).isClosed.measurableSet

/-- HOL `CLOSURE_BIS_LT` (pack2.hl:284). -/
theorem CLOSURE_BIS_LT (u v : Space3) (huv : v ≠ u) :
    closure (bis_lt u v) = bis_le u v := by
  sorry


/-- HOL `VORONOI_OPEN_SUBSET_CLOSED` (pack2.hl:317). -/
theorem VORONOI_OPEN_SUBSET_CLOSED (s : Set Space3) (v : Space3) :
    voronoi_open s v ⊆ voronoi s v := by
  intro x hx w hw
  rcases eq_or_ne w v with rfl | hne
  · exact le_refl _
  · exact le_of_lt (hx w hw hne)

/-- HOL `CLOSURE_VORONOI_OPEN` (pack2.hl:289). -/
theorem CLOSURE_VORONOI_OPEN (s : Set Space3) (v : Space3) :
    closure (voronoi_open s v) = voronoi s v := by
  sorry


/-- HOL `INTERIOR_VORONOI_CLOSED_INTERIOR` (pack2.hl:303). Straggler
(`sorry`): Mathlib only knows `interior (closure X) = interior X` for convex
`X` with nonempty interior
(`Convex.interior_closure_eq_interior_of_nonempty_interior`); the degenerate
case needs the proper-affine-subspace argument. -/
theorem INTERIOR_VORONOI_CLOSED_INTERIOR (s : Set Space3) (v : Space3) :
    interior (voronoi s v) = interior (voronoi_open s v) := by
  sorry

/-- HOL `INTERIOR_VORONOI_CLOSED` (pack2.hl:311). -/
theorem INTERIOR_VORONOI_CLOSED (s : Set Space3) (v : Space3) (hV : Packing s)
    (hs : saturated s) : interior (voronoi s v) = voronoi_open s v := by
  sorry


/-- HOL `MEASURE_VORONOI_CLOSED_OPEN` (pack2.hl:325): the closed and open
cells have equal volume; the symmetric difference is contained in the
frontier of the (convex) open cell, which is null
(`Convex.addHaar_frontier`). -/
theorem MEASURE_VORONOI_CLOSED_OPEN (s : Set Space3) (v : Space3) :
    (volume (voronoi s v)).toReal = (volume (voronoi_open s v)).toReal := by
  sorry


/-- HOL `INTER_VORONOI_SUBSET_BISECTOR` (pack2.hl:337). -/
theorem INTER_VORONOI_SUBSET_BISECTOR (s : Set Space3) (u v : Space3) (hu : u ∈ s)
    (hv : v ∈ s) :
    voronoi s u ∩ voronoi s v ⊆
      {x : Space3 | ((2 : ℝ) • (u - v)) ⬝ᵥ x = ‖u‖ ^ 2 - ‖v‖ ^ 2} := by
  sorry


/-- A hyperplane `{x | ⟪x, a⟫ = b}` with `a ≠ 0` has zero volume. -/
theorem hyperplane_null (a : Space3) (b : ℝ) (ha : a ≠ 0) :
    volume {x : Space3 | inner ℝ x a = b} = 0 := by
  sorry


/-- HOL `NEGLIGIBLE_INTER_VORONOI_CLOSED` (pack2.hl:354). -/
theorem NEGLIGIBLE_INTER_VORONOI_CLOSED (s : Set Space3) (u v : Space3) (hu : u ∈ s)
    (hv : v ∈ s) (huv : u ≠ v) :
    volume (voronoi s u ∩ voronoi s v) = 0 := by
  sorry


/-- HOL `voronoi_closed_version2` (pack2.hl:368). -/
theorem voronoi_closed_version2 (v : Space3) (s : Set Space3) :
    voronoi s v = ⋂ y ∈ (s \ {v}), bis_le v y := by
  ext x
  rw [voronoi, Set.mem_setOf_eq]
  simp only [Set.mem_iInter]
  constructor
  · intro h y hy
    rw [BIS_LE, Set.mem_setOf_eq]
    exact h y hy.1
  · intro h w hw
    rcases eq_or_ne w v with rfl | hne
    · exact le_refl _
    · exact (dist_le_dist_iff x v w).mpr (h w ⟨hw, hne⟩)

/-- HOL `convex_voronoi` (pack2.hl:374), closed-cell form. -/
theorem convex_voronoi_closed (v : Space3) (s : Set Space3) : Convex ℝ (voronoi s v) :=
  CONVEX_VORONOI_CLOSED s v

/-- HOL `bound_voronoi` (pack2.hl:378), closed-cell form. -/
theorem bound_voronoi_closed (v : Space3) (s : Set Space3) (hs : saturated s) :
    Bornology.IsBounded (voronoi s v) :=
  BOUNDED_VORONOI_CLOSED s v hs

/-- HOL `finite_voronoi2` (pack2.hl:383), closed-cell form. -/
theorem finite_voronoi2_closed (v : Space3) (s : Set Space3) (hV : Packing s) :
    {q : Set Space3 |
      ∃ y : Space3, y ∈ s \ {v} ∧ y ∈ Metric.ball v 4 ∧ q = bis_le v y}.Finite := by
  have hEq : {q : Set Space3 |
      ∃ y : Space3, y ∈ s \ {v} ∧ y ∈ Metric.ball v 4 ∧ q = bis_le v y} =
      bis_le v '' ((s ∩ Metric.ball v 4) \ {v}) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_sdiff,
      Set.mem_singleton_iff]
    tauto
  rw [hEq]
  exact ((KIUMVTC' v 4 s hV).sdiff).image (bis_le v)

/-- HOL `not_in_voronoi_closed` (pack2.hl:397). -/
theorem not_in_voronoi_closed (x v : Space3) (s : Set Space3) :
    x ∉ voronoi s v ↔ ∃ y, y ∈ s ∧ y ≠ v ∧ dist x y < dist x v := by
  constructor
  · intro hc2
    by_contra hc3
    push_neg at hc3
    refine hc2 ?_
    intro w hw
    by_cases hwne : w = v
    · subst hwne
      exact le_refl _
    · exact hc3 w hw hwne
  · rintro ⟨y, hy, hyv, hlt⟩ hcell
    exact lt_irrefl _ (hlt.trans_le (hcell y hy))


/-- HOL `voronoi_closed_in_ball` (pack2.hl:403). -/
theorem voronoi_closed_in_ball (x v : Space3) (s : Set Space3) (hV : Packing s)
    (hs : saturated s) (hx : x ∈ voronoi s v) : dist x v < 2 := by
  have h := VORONOI_CLOSED_SUBSET_BALL s v hs hx
  rw [Metric.mem_ball] at h
  exact h


/-- HOL `DRUQUFE` (pack2.hl:411), closed-cell form. -/
theorem DRUQUFE_closed (v : Space3) (s : Set Space3) (hV : Packing s) (hs : saturated s) :
    Convex ℝ (voronoi s v) ∧ Bornology.IsBounded (voronoi s v) ∧
      IsClosed (voronoi s v) ∧ MeasurableSet (voronoi s v) :=
  ⟨CONVEX_VORONOI_CLOSED s v, BOUNDED_VORONOI_CLOSED s v hs, CLOSED_VORONOI_CLOSED s v,
    MEASURABLE_VORONOI_CLOSED s v hs⟩

/-- HOL `measurable_voronoi` (pack2.hl:421), closed-cell form. -/
theorem measurable_voronoi_closed (v : Space3) (s : Set Space3) (hs : saturated s) :
    MeasurableSet (voronoi s v) :=
  MEASURABLE_VORONOI_CLOSED s v hs

/-- HOL `fcc_compatible` (pack2.hl:426): the `fcc_compatible` condition may
be read with either open or closed cells. -/
theorem fcc_compatible_iff_closed (f : Space3 → ℝ) (s : Set Space3) :
    fcc_compatible f s ↔
      ∀ v ∈ s, Real.sqrt 32 ≤ (volume (voronoi s v)).toReal + f v := by
  constructor
  · intro h v hv
    rw [MEASURE_VORONOI_CLOSED_OPEN s v]
    exact h v hv
  · intro h v hv
    have h' := h v hv
    rw [MEASURE_VORONOI_CLOSED_OPEN s v] at h'
    exact h'


/-- HOL `voronoi_closed_subset_ball` (pack2.hl:431). -/
theorem voronoi_closed_subset_ball (v : Space3) (s : Set Space3) (hs : saturated s) :
    voronoi s v ⊆ Metric.ball v 2 :=
  VORONOI_CLOSED_SUBSET_BALL s v hs

/-- HOL `all_voronoi_closed_subset_ball` (pack2.hl:436). -/
theorem all_voronoi_closed_subset_ball (v : Space3) (s : Set Space3) (p : Space3) (r : ℝ)
    (hV : Packing s) (hs : saturated s) (hv : v ∈ Metric.ball p (r + 1)) :
    voronoi s v ⊆ Metric.ball p (r + 3) := by
  intro x hx
  rw [Metric.mem_ball] at hv ⊢
  have h1 : dist p x ≤ dist p v + dist x v := by
    linarith [dist_triangle p v x, dist_comm v x]
  have h2 : dist x v < 2 := by
    have h3 := VORONOI_CLOSED_SUBSET_BALL s v hs hx
    rw [Metric.mem_ball] at h3
    exact h3
  linarith [Metric.mem_ball.mp hv, h1, h2, dist_comm x p, dist_comm v p]

/-- HOL `unions_voronoi_closed_subset_ball` (pack2.hl:451). -/
theorem unions_voronoi_closed_subset_ball (s : Set Space3) (p : Space3) (r : ℝ)
    (hV : Packing s) (hs : saturated s) :
    (⋃ v ∈ Metric.ball p (r + 1), voronoi s v) ⊆ Metric.ball p (r + 3) := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
  exact all_voronoi_closed_subset_ball v s p r hV hs hv hxv

/-- HOL `unions_voronoi_closed_center_in_ball_subset_ball` (pack2.hl:459). -/
theorem unions_voronoi_closed_center_in_ball_subset_ball (s : Set Space3) (p : Space3)
    (r : ℝ) (hV : Packing s) (hs : saturated s) :
    (⋃ v ∈ (s ∩ Metric.ball p (r + 1)), voronoi s v) ⊆ Metric.ball p (r + 3) := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
  exact all_voronoi_closed_subset_ball v s p r hV hs hv.2 hxv

/-- HOL `finite_set_voronoi_center_in_ball` (pack2.hl:471), closed-cell
form. -/
theorem finite_set_voronoi_center_in_ball_closed (s : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing s) :
    {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
      v ∈ s ∩ Metric.ball p (r + 1) ∧ w = s ∧ q = voronoi w v}.Finite := by
  sorry


/-- HOL `measurable_unions_voronoi` (pack2.hl:480), closed-cell form. -/
theorem measurable_unions_voronoi_closed (s : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing s) (hs : saturated s) :
    MeasurableSet (⋃ v ∈ (s ∩ Metric.ball p (r + 1)), voronoi s v) := by
  sorry


/-- HOL `measure_unions_sum_voronoi` (pack2.hl:491), closed-cell form. -/
theorem measure_unions_sum_voronoi_closed (s : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing s) (hs : saturated s)
    (hfin : (s ∩ Metric.ball p (r + 1)).Finite) :
    (volume (⋃ v ∈ (s ∩ Metric.ball p (r + 1)), voronoi s v)).toReal =
      ∑ v ∈ hfin.toFinset, (volume (voronoi s v)).toReal := by
  sorry



/-- HOL `sum_measure_voronoi_closed_le_ball` (pack2.hl:504). -/
theorem sum_measure_voronoi_closed_le_ball (s : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing s) (hs : saturated s)
    (hfin : (s ∩ Metric.ball p (r + 1)).Finite) :
    ∑ v ∈ hfin.toFinset, (volume (voronoi s v)).toReal ≤
      (volume (Metric.ball p (r + 3))).toReal := by
  sorry



/-- HOL `ineq_lm5_3_step3` (pack2.hl:512), closed-cell form. -/
theorem ineq_lm5_3_step3_closed (s : Set Space3) (p : Space3) (r : ℝ) (A : Space3 → ℝ)
    (hr : 0 ≤ r) (hV : Packing s) (hs : saturated s) (hfcc : fcc_compatible A s)
    (hfin : (s ∩ Metric.ball p (r + 1)).Finite) :
    Real.sqrt 32 * ((s ∩ Metric.ball p (r + 1)).ncard : ℝ) ≤
      ∑ v ∈ hfin.toFinset, (A v + (volume (voronoi s v)).toReal) := by
  have hfcc' := (fcc_compatible_iff_closed A s).mp hfcc
  have h1 : ∑ v ∈ hfin.toFinset, Real.sqrt 32 ≤
      ∑ v ∈ hfin.toFinset, (A v + (volume (voronoi s v)).toReal) := by
    refine Finset.sum_le_sum fun v hv => ?_
    have hvT : v ∈ (s ∩ Metric.ball p (r + 1)) := hfin.mem_toFinset.mp hv
    have hh := hfcc' v hvT.1
    linarith
  have h2 : Real.sqrt 32 * ((s ∩ Metric.ball p (r + 1)).ncard : ℝ) =
      ∑ v ∈ hfin.toFinset, Real.sqrt 32 := by
    rw [Set.ncard_eq_toFinset_card (s ∩ Metric.ball p (r + 1)) hfin, Finset.sum_const,
      nsmul_eq_mul]
    exact mul_comm _ _
  rw [h2]
  exact h1



end

end Kepler.Text
