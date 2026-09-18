/-
PackingAuto20: port of `scripts/packing/TSKAJXY1.hl` (Flyspeck chapter
"TSKAJXY", Vu Khac Ky 2012, 5668 lines).

FILE MAP (TSKAJXY hub role)
  TSKAJXY1 is the HUB of the TSKAJXY special-case chain 1 -> 2 -> 3: it
  carries (a) the analytic toolkit that reduces `mcell` invariants
  (`dihX`, `sol`, `volume.real`, `gammaX`) to the 6-argument nonlinear
  functions `dih_y/sol_y/vol_y/gamma4fgcy/gamma3f` on the edge-length
  six-tuple `y1..y6`, and (b) the raw numeric bound `HJKDESR1a_1cell`
  feeding the TSKAJXY inequality.  The later chain links (TSKAJXY2/3)
  consume exactly these six theorems; the small bank below
  (SET_RULE-style set algebra + `KY_COPLANAR_3`,
  `NEGLIGIBLE_MEASURE_UNION_klema`) is re-exported-style support shared
  by the whole chain, mirroring the file's restored SET_TAC preamble
  ("Changed by Vu Khac Ky - 15 Nov 2012").

  Source layout: no `new_definition` at all (0 defs in .hl).  Two tactic
  shims (`SET_TAC` restored, `SET_RULE tm = prove(tm,SET_TAC[])`), three
  small lemmas, six giant `prove_by_refinement` theorems whose bodies
  inline ~206 SET_RULE facts (97 distinct instances, ~25 generic
  patterns) -- those instances are lifted here into a generic private
  support-lemma bank (all `p20_*`, proved; they are the mechanical
  set-algebra core the giants rewrite through).

ENCODING NOTES
  - HOL `dih_y/sol_y/vol_y/gamma4fgcy/gamma3f` (sphere.hl:159-582): the
    `delta_x4/dih_x/dih_y/sol_y` half of this payload now resolves to
    Kepler.Text.SphereKit (atn2-merge, plan §5.2); the vol/gamma family (`vol_x/vol_y/vol4f/
    gamma4fgcy/vol3r/vol3f/gamma3f`) stays here (its only duplicate was
    PackingAuto21's verbatim copy, deleted in wave 2).  The hub's
    `deltaXf`/`deltaX4f` names survive as compatibility aliases of
    SphereKit `deltaX`/`deltaX4` until the wave-3 renames.
  - HOL `real^3` <-> `V3` (Kepler.Geom); `dist (u,v)` <-> `dist u v`;
    `NULLSET X` <-> `nullSet X` (`volume X = 0`); `vol X` (real volume)
    <-> `volume.real X`, matching the convention inside `gammaX`;
    `coplanar` <-> `Coplanar ℝ`; `convex hull` <-> `convexHull ℝ`;
    `aff_ge` <-> `affGe` (Kepler.Geom.Aff); `sqrt2` <-> `Real.sqrt 2`.
  - HOL hypothesis lists `a = dihV ... /\ ...` become explicit
    hypotheses; free HOL variables are universally closed.
  - DISCHARGES: none.  No `pack_concl` interface matches these
    conclusions: they are upstream support FOR the chain -- the chain's
    concl `TSKAJXY_statement` (PackingAuto2.lean:845,
    `criticalEdgeX`-based) is discharged by TSKAJXY2/3, not here.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.SphereKit
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Definitional payload: the sphere.hl nonlinear toolkit

Single-sourced in `Kepler.Text.SphereKit` (atn2-merge, docs/atn2-merge-plan.md
§5.2); that module declares the kit in this same `Kepler.Text` namespace, so
deleting the hub's local defs keeps every plain name resolving for the whole
TSKAJXY chain (and the LocalAuto2 lane).  The hub's historical
`deltaXf`/`deltaX4f` names survive as compatibility alias defs (bodies kept
VERBATIM, definitionally equal to SphereKit `deltaX`/`deltaX4`: the
LocalAuto2-lane proofs close goals by `simp only [deltaXf, …]` + `ring`,
which needs the alias to unfold all the way to the arithmetic body).  Wave 3
renames their users (plan §4) and removes them. -/

/-- Compatibility alias for the hub's historical `delta_x` name (verbatim
body = SphereKit `deltaX` = the old PackingAuto20.lean:73 def); removed in
wave 3 together with the `deltaXf → deltaX` user renames. -/
def deltaXf (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
    x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

/-- Compatibility alias for the historical `delta_x4` name (verbatim body =
SphereKit `deltaX4` = the old PackingAuto20.lean:80 def); removed in wave 3
together with `deltaXf`. -/
noncomputable def deltaX4f (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `vol_x` (sphere.hl:251): simplex volume from squared lengths. -/
noncomputable def volXf (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) / 12

/-- HOL `vol_y` (sphere.hl:547, `y_of_x vol_x`). -/
noncomputable def volY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  volXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `vol4f` (sphere.hl:568): fake 4-cell volume. -/
noncomputable def vol4f (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
      solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3) -
    (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
      f (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
      f (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
      f (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
      f (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
      f (y6 / 2) * dihY y6 y1 y5 y3 y4 y2)

/-- HOL `gamma4f` (sphere.hl:574) and `gamma4fgcy` (sphere.hl:566, its
definitionally equal alias kept as a separate name for the TSKAJXY
statement surface). -/
noncomputable def gamma4fgcy (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  volY y1 y2 y3 y4 y5 y6 - vol4f y1 y2 y3 y4 y5 y6 f

/-- HOL `vol3r` (sphere.hl:578): real 3-cell volume. -/
noncomputable def vol3r (y1 y2 y3 r : ℝ) : ℝ := volY r r r y1 y2 y3

/-- HOL `vol3f` (sphere.hl:580): fake 3-cell volume. -/
noncomputable def vol3f (y1 y2 y3 r : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (solY y1 y2 r r r y3 + solY y2 y3 r r r y1 + solY y3 y1 r r r y2) -
    (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dihY y1 y2 r r r y3 +
      f (y2 / 2) * dihY y2 y3 r r r y1 +
      f (y3 / 2) * dihY y3 y1 r r r y2)

/-- HOL `gamma3f` (sphere.hl:582). -/
noncomputable def gamma3f (y1 y2 y3 r : ℝ) (f : ℝ → ℝ) : ℝ :=
  vol3r y1 y2 y3 r - vol3f y1 y2 y3 r f

/-! ## Small caps of the hub -/

/-- HOL `KY_COPLANAR_3` (TSKAJXY1.hl:88): any three points are coplanar. -/
theorem KY_COPLANAR_3 (a b c : V3) : Coplanar ({a, b, c} : Set V3) :=
  Kepler.Geom.coplanar_triple a b c

/-- HOL `NEGLIGIBLE_MEASURE_UNION_klema` (TSKAJXY1.hl:96). -/
theorem NEGLIGIBLE_MEASURE_UNION_klema {s t : Set V3} (_hs : MeasurableSet s)
    (_ht : MeasurableSet t) (hnt : nullSet t) :
    volume.real (s ∪ t) = volume.real s := by
  have h1 : volume (s ∪ t) ≤ volume s := by
    refine le_trans (measure_union_le s t) ?_
    rw [show volume t = 0 from hnt, add_zero]
  have h2 : volume s ≤ volume (s ∪ t) :=
    measure_mono (Set.subset_union_left (s := s) (t := t))
  exact congrArg ENNReal.toReal (le_antisymm h1 h2)

/-! ## The six ALL-CAPS theorems (giant `prove_by_refinement` bodies: sorry)

HOL bodies inline ~206 SET_RULE facts + geometric heavy machinery
(SOLID_J_, MCELL_EXPLICIT, Flyspeck_constants.bounds, ...); the proofs
are out of scope here -- the statements are the chain interface. -/

/- HOL `AFF_GE_1_3` (TSKAJXY1.hl:75, proof `AFF_TAC`): explicit cone
formula for `aff_ge` of a point-triple disjoint from the apex.
DISCHARGES: identical interface already ported AND proved as
`PlanarityAuto11.AFF_GE_1_3` (PlanarityAuto11.lean:1136, same
statement modulo variable renaming); the hub's re-derivation is not
re-declared here. -/
/-- HOL `SOL_SOLID_TRIANGLE` (TSKAJXY1.hl:111): the solid angle of a
vertex of a (non-coplanar) tetrahedron is the spherical excess. -/
theorem SOL_SOLID_TRIANGLE {a b c : ℝ} (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3))
    (ha : a = dihV v0 v1 v2 v3) (hb : b = dihV v0 v2 v3 v1)
    (hc : c = dihV v0 v3 v1 v2) :
    sol v0 (convexHull ℝ ({v0, v1, v2, v3} : Set V3)) = a + b + c - Real.pi := by
  sorry

/-- HOL `DIHX_DIH_Y_lemma` (TSKAJXY1.hl:567): the six dihedral angles of
a saturated-packing 4-cell are the `dih_y` values of the edge-length
six-tuple (per the per-edge argument permutation). -/
theorem DIHX_DIH_Y_lemma (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3) (i : ℕ)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hi : 4 ≤ i) (hX : X = mcell i V ul) (hn : ¬ nullSet X)
    (hul : ul = [u0, u1, u2, u3]) (hy1 : dist u0 u1 = y1) (hy2 : dist u0 u2 = y2)
    (hy3 : dist u0 u3 = y3) (hy4 : dist u2 u3 = y4) (hy5 : dist u1 u3 = y5)
    (hy6 : dist u1 u2 = y6) :
    dihX V X (u0, u1) = dihY y1 y2 y3 y4 y5 y6 ∧
      dihX V X (u0, u2) = dihY y2 y3 y1 y5 y6 y4 ∧
      dihX V X (u0, u3) = dihY y3 y1 y2 y6 y4 y5 ∧
      dihX V X (u2, u3) = dihY y4 y3 y5 y1 y6 y2 ∧
      dihX V X (u1, u3) = dihY y5 y1 y6 y2 y4 y3 ∧
      dihX V X (u1, u2) = dihY y6 y1 y5 y3 y4 y2 := by
  sorry

/-- HOL `SOL_SOL_Y_EXPLICIT` (TSKAJXY1.hl:2995): the four vertex solid
angles of a 4-cell are the `sol_y` values of the edge six-tuple. -/
theorem SOL_SOL_Y_EXPLICIT (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3) (i : ℕ)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hi : 4 ≤ i) (hX : X = mcell i V ul) (hn : ¬ nullSet X)
    (hul : ul = [u0, u1, u2, u3]) (hy1 : dist u0 u1 = y1) (hy2 : dist u0 u2 = y2)
    (hy3 : dist u0 u3 = y3) (hy4 : dist u2 u3 = y4) (hy5 : dist u1 u3 = y5)
    (hy6 : dist u1 u2 = y6) :
    sol u0 X = solY y1 y2 y3 y4 y5 y6 ∧
      sol u1 X = solY y1 y5 y6 y4 y2 y3 ∧
      sol u2 X = solY y4 y2 y6 y1 y5 y3 ∧
      sol u3 X = solY y4 y5 y3 y1 y2 y6 := by
  sorry

/-- HOL `gammaX_gamm4fgcy` (TSKAJXY1.hl:3508): volume and `gammaX` of a
4-cell are the analytic `vol_y` / `gamma4fgcy` of the edge six-tuple. -/
theorem gammaX_gamm4fgcy (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3) (i : ℕ)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hi : 4 ≤ i) (hX : X = mcell i V ul) (hn : ¬ nullSet X)
    (hul : ul = [u0, u1, u2, u3]) (hy1 : dist u0 u1 = y1) (hy2 : dist u0 u2 = y2)
    (hy3 : dist u0 u3 = y3) (hy4 : dist u2 u3 = y4) (hy5 : dist u1 u3 = y5)
    (hy6 : dist u1 u2 = y6) :
    volume.real X = volY y1 y2 y3 y4 y5 y6 ∧
      gammaX V X lmfun = gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  sorry

/-- HOL `gammaX_gamma3f` (TSKAJXY1.hl:4178): same for a 3-cell: all
`sqrt2`-legs `y1 y2 y3` collapsed to `sqrt2`. -/
theorem gammaX_gamma3f (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3)
    (y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hX : X = mcell 3 V ul) (hn : ¬ nullSet X) (hul : ul = [u0, u1, u2, u3])
    (hy4 : dist u1 u2 = y4) (hy5 : dist u0 u2 = y5) (hy6 : dist u0 u1 = y6) :
    volume.real X = volY (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 ∧
      sol u0 X = solY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 ∧
      sol u1 X = solY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5 ∧
      sol u2 X = solY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 ∧
      dihX V X (u0, u1) = dihY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5 ∧
      dihX V X (u0, u2) = dihY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 ∧
      dihX V X (u1, u2) = dihY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 ∧
      gammaX V X lmfun = gamma3f y4 y5 y6 (Real.sqrt 2) lmfun := by
  sorry

/-- HOL `HJKDESR1a_1cell` (TSKAJXY1.hl:5652): numeric seed of the chain
(proof route: `3 * mm1 < 3 * 1.3 < pi * sqrt 2` via certified bounds of
`Flyspeck_constants.bounds`, not re-derivable without interval tactics). -/
theorem HJKDESR1a_1cell : 0 < 8 * Real.pi * Real.sqrt 2 / 3 - 8 * mm1 := by
  sorry

/-! ## Support-lemma bank (generic forms of the hub's ~206 inlined
SET_RULE facts; private + proved) -/

private theorem p20_memPair {α : Type*} {x a b : α} :
    x ∈ ({a, b} : Set α) ↔ x = a ∨ x = b := by
  simp

private theorem p20_memTriple {α : Type*} {x a b c : α} :
    x ∈ ({a, b, c} : Set α) ↔ x = a ∨ x = b ∨ x = c := by
  simp

private theorem p20_memQuadruple {α : Type*} {x a b c d : α} :
    x ∈ ({a, b, c, d} : Set α) ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by
  simp

private theorem p20_memQuintuple {α : Type*} {x a b c d e : α} :
    x ∈ ({a, b, c, d, e} : Set α) ↔ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  simp

private theorem p20_memSextuple {α : Type*} {x a b c d e f : α} :
    x ∈ ({a, b, c, d, e, f} : Set α) ↔
      x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  simp

private theorem p20_four_in_nats : (4 : ℕ) ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by simp

private theorem p20_three_in_nats : (3 : ℕ) ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by simp

private theorem p20_three_in_twothree : (3 : ℕ) ∈ ({2, 3} : Set ℕ) := by simp

private theorem p20_pair_comm {α : Type*} (a b : α) : ({a, b} : Set α) = {b, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup12 {α : Type*} (a b c : α) :
    ({a, a, b, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup13 {α : Type*} (a b c : α) :
    ({a, b, a, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup14 {α : Type*} (a b c : α) :
    ({a, b, c, a} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup23 {α : Type*} (a b c : α) :
    ({a, b, b, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup24 {α : Type*} (a b c : α) :
    ({a, b, c, b} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup34 {α : Type*} (a b c : α) :
    ({a, b, c, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap12 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {b, a, c, d} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap13 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {c, b, a, d} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap14 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {d, b, c, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap23 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {a, c, b, d} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap24 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {a, d, c, b} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap34 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {a, b, d, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_rot {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {b, c, d, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_rotBack {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {d, a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_union_single {α : Type*} (a b c d : α) :
    ({a, b, c} : Set α) ∪ {d} = ({a, b, c, d} : Set α) := by
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_member_subset {α : Type*} {a : α} {t : Set α}
    (h : ∃ s : Set α, a ∈ s ∧ s ⊆ t) : a ∈ t := by
  obtain ⟨s, ha, hst⟩ := h
  exact hst ha

private theorem p20_subset_antisymm {α : Type*} {A B : Set α} (h1 : A ⊆ B)
    (h2 : B ⊆ A) : A = B := Subset.antisymm h1 h2

private theorem p20_inter_subset_right {α : Type*} (a s : Set α) :
    a ∩ s ⊆ s := Set.inter_subset_right

private theorem p20_inter_subset_inter_left {α : Type*} {s t : Set α} (c : Set α)
    (h : s ⊆ t) : s ∩ c ⊆ t ∩ c := Set.inter_subset_inter_left c h

private theorem p20_inter_distrib_left {α : Type*} (a b c : Set α) :
    a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := Set.inter_union_distrib_left a b c

private theorem p20_inter_comm {α : Type*} (a b : Set α) : a ∩ b = b ∩ a :=
  Set.inter_comm a b

private theorem p20_disjoint_sing_triple (v0 v1 v2 v3 : V3) :
    ({v0} : Set V3) ∩ {v1, v2, v3} = ∅ ↔
      ¬(v0 = v1 ∨ v0 = v2 ∨ v0 = v3) := by
  constructor
  · intro h heq
    have hm : v0 ∈ ({v0} : Set V3) ∩ {v1, v2, v3} := by
      rcases heq with heq | heq | heq <;>
        exact Set.mem_inter (by simp) (by rw [heq]; simp)
    rw [h] at hm
    exact absurd hm (by simp)
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hx0, hx2⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx2
    exact h (hx0 ▸ hx2)

private theorem p20_quad_subset (V : Set V3) (u0 u1 u2 u3 : V3) :
    u0 ∈ V ∧ u1 ∈ V ∧ u2 ∈ V ∧ u3 ∈ V ↔ ({u0, u1, u2, u3} : Set V3) ⊆ V := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ x hx
    rcases p20_memQuadruple.mp hx with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    exact ⟨h (by simp), h (by simp), h (by simp), h (by simp)⟩
