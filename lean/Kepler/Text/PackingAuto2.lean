/-
Port of the HOL Light Flyspeck Packing chapter, definition layer:
`scripts/packing/pack_defs.hl` (213 lines: the Marchal cell decomposition
`mcell0`–`mcell4` and its 51-definition support kit) plus the chapter's
conclusion statements `scripts/packing/pack_concl.hl` (344 lines: all
`*_concl` capstone statement placeholders).

Porting method: skeleton (definitions verbatim-faithful + per-definition
HOL docstrings; conclusion statements frozen with `by sorry` bodies, to be
filled by the auto_loop harness).

## File map

1. Support conventions (sums over sets, `HD`/`EL` junk values, `TABLE`/
   `REVERSE_TABLE`/`DROP`/`left_action`/`left_action_list`, `permutes`,
   `affine_dependent`, `NULLSET`).
2. Sphere-chapter primitives needed by pack_defs (ported verbatim from
   Flyspeck `general/sphere.hl`, persistent copy
   `/dev/shm/kepler-ref/flyspeck/text_formalization/general/sphere.hl`;
   each def cites its line). These are shared infrastructure: later lanes
   should delete their copies and import this file instead (precedent:
   `Kepler/Text/Polytope.lean` merge note).
3. The 51 `pack_defs.hl` definitions (`mcell0`–`mcell4`, `cell_params`,
   `left_action_list`, `gammaX`, `cell_cluster`, ...).
4. The `pack_concl.hl` statements: 52 theorems `*_concl` + the definition
   `TSKAJXY_statement`, all with `by sorry` bodies.

## Encoding notes

- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  `dot` ↔ `⬝ᵥ`; `vec 0` ↔ `(0 : V3)`; `x % r` ↔ `r • x`.
- HOL `packing` ↔ `Packing` (Kepler/Statement.lean:35, the canonical chapter
  statement; manifest docs/packing-manifest.md §3). `saturated`
  (sphere.hl:439) is ported HERE: the manifest assigns it to the pack_defs
  wave ("not yet on Lean side — port with pack_defs wave").
- **Marchal cells (mcell0–mcell4).** The cells are Set-valued functions of
  `(V : Set V3)` and an ordered 4-point list `ul : List V3` (HOL
  `(real^3)list`), NOT of an abstract simplex type: each `mcellN` is a
  guarded `if ... then REGION else ∅` where the guard reads the circumradius
  chain `hl (truncate_simplex j ul)` (`hl` = circumradius of the point set,
  measured half-length for pairs) and the region is cut out of the Rogers
  simplex `rogers V ul` by balls and radial cones (`rcone_gt`/`rcone_ge`)
  around the edges from `HD ul`. This set-valued-if encoding is kept
  verbatim because the whole chapter (EMNWUUS, SLTSTLO, URRPHBZ, LEPJBDJ,
  TSKAJXY, ...) reasons about cell emptiness, measurability and
  intersections of exactly these set expressions. `mcell i V ul` dispatches
  on `i : ℕ` (0..4, else mcell4); `mcell_set` collects all cells over
  `barV V 3` lists.
- List junk values: HOL `HD`/`TL`/`EL` are junk on out-of-range indices; we
  use `List.headD`/`List.getD` with default `0` (same junk-value convention
  as `Kepler.Geom.linCombo` in Kepler/Geom/Aff.lean). `left_action_list` and
  `DROP` are generic and take an `[Inhabited α]` default.
- HOL `sum S f` over a set is only meaningful for finite `S`; rendered as
  `setSum` (0 on infinite sets, `linCombo` convention).
- HOL `@` ↔ `Classical.epsilon` (convention of Kepler/Text/Fan.lean);
  `truncate_simplex`, `circumcenter`, `radV`, `mxi`, `cell_params`,
  `cell_params_d`, `hminus` are literal epsilon ports of sphere.hl:327/369/
  371 and pack_defs.hl:39/84/115/153.
- HOL `closest_point` (sphere.hl:332 usage) has no Mathlib counterpart in
  this snapshot: ported as `closestPoint` by `Classical.epsilon` over the
  HOL Light defining property `y IN K /\ !z IN K ==> dist x y <= dist x z`.
- `vol` ↔ `volume.real` (real-valued Lebesgue volume, Kepler/Geom/
  Volume.lean idiom); `measurable` ↔ `MeasurableSet`; `NULLSET X` ↔
  `nullSet X` (`volume X = 0` in ENNReal; for Lebesgue measure this entails
  measurability by completeness). HOL `measure` ↔ `volume.real`.
- Pack1-owned definitions (pack1.hl defines `map3`, `voronoi_open`, `bis`,
  `nua_kg`, `saturated`, plus duplicates of `negligible_fun_p` and
  `fcc_compatible`): we do NOT import `Kepler.Text.PackingAuto1` (parallel
  worker). `voronoi_open` and `bis` are ported here as PRIVATE copies
  (precedent: the private Polytope copies in PolyAuto4/5/6; merge note:
  delete these when PackingAuto1 lands). `saturated` is public here by
  manifest assignment; `negligible_fun_p`/`fcc_compatible` are public here
  because they are part of the 51 pack_defs definitions (pack1's copies are
  the duplicates — merge-time cleanup). `-- NEEDS: PackingAuto1.*` markers
  at the private copies.
- `marchal_quartic` is commented out in pack_defs.hl:134-138 but used by
  `marchal`/`hminus`; we port the ACTIVE definition from sphere.hl:519
  (it differs from the commented draft).
- Name mapping (HL → Lean): camelCase per repo convention, opaque Flyspeck
  IDs kept verbatim (`mcell0`, `VX`, `edgeX`, `*_concl`, ...). Full mapping
  in the per-definition docstrings.
- Affine vocabulary: `affine hull` ↔ `(affineSpan ℝ s : Set V3)`,
  `aff_dim` ↔ `affDim` (Kepler/Text/Polytope.lean), `face_of`/`facet_of` ↔
  `FaceOf`/`FacetOf`, `aff_ge` ↔ `affGe` (Kepler/Geom/Aff.lean),
  `convex hull` ↔ `convexHull ℝ`, `CARD` ↔ `Nat.card` (junk 0 on infinite
  sets, matching HOL), `extreme_point_of` ↔ `Set.extremePoints ℝ`.
- `topological_component_yfan` already exists as
  `Kepler.Text.Fan.topologicalComponentYfan (x : V3) (V : Set V3)
  (E : Set (Set V3))`; HOL passes the fan as a pair `(V,E)`, rendered here
  as the two components of `fanOfPolyhedron s`.
- Constants `sqrt2`/`sqrt8` (sphere.hl:76/75) and `asn` are inlined as
  `Real.sqrt 2`, `Real.sqrt 8`, `Real.arcsin`.
- Statements of pack_concl with FREE HOL variables (implicitly universally
  closed in HOL): `REUHADY_concl`/`REUHADY_concl_version2` use `w1 w2`, and
  `IVFICRK_concl` uses `i σ` inside its second conjunct; both are bound
  explicitly in Lean (noted in the respective docstrings).
- `vor_list` (used only by KHEJKCI_concl) is NOT defined in any local HL
  source (book sphere.hl has `voronoi_nondg` instead); ported as the
  documented reconstruction `vorList V k ul := barV V k ul /\ hl ul < sqrt 2`,
  to be reconciled against core Flyspeck `Sphere.vor_list` at fill-in time.
- NOT ported: the pack_concl.hl cross-references `Sphere.BARV`,
  `Sphere.OMEGA_LIST`, `Sphere.ROGERS`, `Sphere.VORONOI_*` (they are defs,
  ported here), and the commented-out `OAPVION_concl`, `XNHPWAB3` draft,
  `IJEKNGA`, `JGXZYGW`.
-/

import Kepler.Text.Polytope
import Kepler.Text.Fan
import Kepler.Text.PackingJGXZYGW
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

noncomputable section

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Support conventions -/

/-- HOL `sum S f` for a set `S` (junk on infinite sets; here `0`, same
convention as `Kepler.Geom.linCombo`, Kepler/Geom/Aff.lean:28). -/
def setSum {α : Type*} (s : Set α) (f : α → ℝ) : ℝ :=
  if h : Set.Finite s then ∑ w ∈ h.toFinset, f w else 0

/-- HOL `HD` on `real^3` lists (junk on `[]`; here `0`). -/
def hdV (ul : List V3) : V3 := ul.headD 0

/-- HOL `EL i ul` on `real^3` lists (junk out of range; here `0`). -/
def elV (ul : List V3) (i : ℕ) : V3 := ul.getD i 0

/-- HOL `REVERSE_TABLE` (pack_defs.hl:28-29), by primitive recursion. -/
def reverseTable {α : Type*} (f : ℕ → α) : ℕ → List α
  | 0 => []
  | i + 1 => f i :: reverseTable f i

/-- HOL `TABLE` (pack_defs.hl:31): `TABLE f k = REVERSE (REVERSE_TABLE f k)`. -/
def table {α : Type*} (f : ℕ → α) (k : ℕ) : List α := (reverseTable f k).reverse

/-- HOL `DROP` (pack_defs.hl:37): removes the `i`-th element
(`DROP ul 0 = TL ul`, `DROP ul (SUC i) = HD ul :: DROP (TL ul) i`).
Distinct from `List.drop`. -/
def dropIth {α : Type*} [Inhabited α] (ul : List α) : ℕ → List α
  | 0 => ul.tail
  | i + 1 => ul.headD default :: dropIth ul.tail i

/-- HOL `left_action` (pack_defs.hl:33): `left_action p f x = f (inverse p x)`. -/
def leftAction {α : Type*} {β : Type*} (p : Equiv.Perm α) (f : α → β) (x : α) : β :=
  f (p.symm x)

/-- HOL `left_action_list` (pack_defs.hl:35):
`TABLE (\i. EL (inverse p i) ul) (LENGTH ul)`. The `Inhabited` default only
affects out-of-range indices (HOL junk), never the in-range behavior used by
the chapter (permutations of `0..LENGTH ul - 1`). -/
def leftActionList {α : Type*} [Inhabited α] (p : Equiv.Perm ℕ) (ul : List α) : List α :=
  (List.range ul.length).map fun i => ul.getD (p.symm i) default

/-- HOL Light `p permutes s`: `!x. x IN s <=> p x IN s` (with `p` a typed
permutation `Equiv.Perm ℕ`, matching flyspeck's usage `p permutes (0..k)`
together with `inverse p`). -/
def permutes (p : Equiv.Perm ℕ) (s : Set ℕ) : Prop := ∀ x, x ∈ s ↔ p x ∈ s

/-- HOL `affine_dependent S` for a set (Mathlib's `AffineIndependent` is
family-indexed; we index by the coercion `↥S`). -/
def affineDependent (S : Set V3) : Prop :=
  ¬ AffineIndependent ℝ (fun x : S => (x : V3))

/-- Flyspeck `NULLSET X`: measure zero. Rendered as `volume X = 0` in
`ℝ≥0∞`; for Lebesgue measure this entails `MeasurableSet X` by completeness. -/
def nullSet (X : Set V3) : Prop := volume X = 0

/-- HOL Light `closest_point K x` (used at sphere.hl:332):
`@y. y IN K /\ !z. z IN K ==> dist(x,y) <= dist(x,z)`. -/
def closestPoint (K : Set V3) (x : V3) : V3 :=
  Classical.epsilon fun y => y ∈ K ∧ ∀ z ∈ K, dist x y ≤ dist x z

/-! ## Sphere-chapter primitives (general/sphere.hl) -/

/-- HOL `set_of_list` (azure sets.ml:2492): `h INSERT set_of_list t`. -/
def setOfList {α : Type*} (ul : List α) : Set α := {x | x ∈ ul}

/-- HOL `initial_sublist` (sphere.hl:321): `?yl. zl = APPEND xl yl`. -/
def initialSublist (xl zl : List V3) : Prop := ∃ yl, zl = xl ++ yl

/-- HOL `voronoi_open` (sphere.hl:304; also pack1.hl:153).
NEEDS: PackingAuto1.voronoi_open — private copy, delete when PackingAuto1
lands (parallel worker owns pack1.hl). -/
private def voronoiOpen (V : Set V3) (v : V3) : Set V3 :=
  {x | ∀ w ∈ V, w ≠ v → dist x v < dist x w}

/-- HOL `voronoi_closed` (sphere.hl:307). -/
def voronoiClosed (V : Set V3) (v : V3) : Set V3 :=
  {x | ∀ w ∈ V, dist x v ≤ dist x w}

/-- HOL `voronoi_set` (sphere.hl:310): `INTERS {voronoi_closed V v | v IN W}`. -/
def voronoiSet (V W : Set V3) : Set V3 := ⋂₀ {voronoiClosed V v | v ∈ W}

/-- HOL `voronoi_list` (sphere.hl:314): `voronoi_set V (set_of_list wl)`. -/
def voronoiList (V : Set V3) (ul : List V3) : Set V3 := voronoiSet V (setOfList ul)

/-- HOL `voronoi_nondg` (sphere.hl:317). -/
def voronoiNondg (V : Set V3) (ul : List V3) : Prop :=
  ul.length < 5 ∧ setOfList ul ⊆ V ∧ affDim (voronoiList V ul) + (ul.length : ℤ) = 4

/-- HOL `barV` (sphere.hl:324): `LENGTH ul = k+1 /\ !vl. initial_sublist vl ul /\
0 < LENGTH vl ==> voronoi_nondg V vl`. -/
def barV (V : Set V3) (k : ℕ) (ul : List V3) : Prop :=
  ul.length = k + 1 ∧ ∀ vl, initialSublist vl ul ∧ 0 < vl.length → voronoiNondg V vl

/-- HOL `truncate_simplex` (sphere.hl:327): the prefix of length `j+1`,
selected by `@vl. LENGTH vl = j+1 /\ initial_sublist vl ul`. -/
def truncateSimplex (j : ℕ) (ul : List V3) : List V3 :=
  Classical.epsilon fun vl => vl.length = j + 1 ∧ initialSublist vl ul

/-- HOL `omega_list_n` (sphere.hl:331, recursive): `omega_list_n V ul 0 = HD ul`,
`omega_list_n V ul (SUC i) = closest_point (voronoi_list V
(truncate_simplex (SUC i) ul)) (omega_list_n V ul i)`. -/
def omegaListN (V : Set V3) (ul : List V3) : ℕ → V3
  | 0 => hdV ul
  | i + 1 => closestPoint (voronoiList V (truncateSimplex (i + 1) ul)) (omegaListN V ul i)

/-- HOL `omega_list` (sphere.hl:335): `omega_list_n V ul (LENGTH ul - 1)`. -/
def omegaList (V : Set V3) (ul : List V3) : V3 := omegaListN V ul (ul.length - 1)

/-- HOL `rogers` (sphere.hl:338): `convex hull (IMAGE (omega_list_n V ul)
{j | j < LENGTH ul})` — the hull of the successive closest-point projections
(the Rogers simplex of this formalization). -/
def rogers (V : Set V3) (ul : List V3) : Set V3 :=
  convexHull ℝ (omegaListN V ul '' {j : ℕ | j < ul.length})

/-- HOL `bis` (sphere.hl:360). NEEDS: PackingAuto1.bis — private copy, delete
when PackingAuto1 lands. -/
private def bis (u v : V3) : Set V3 := {x | dist x u = dist x v}

/-- HOL `bis_le` (sphere.hl:362). -/
def bisLe (u v : V3) : Set V3 := {x | dist x u ≤ dist x v}

/-- HOL `circumcenter` (sphere.hl:369): `@v. (affine hull S) v /\
(?c. !w. S w ==> c = dist(v,w))`. -/
def circumcenter (S : Set V3) : V3 :=
  Classical.epsilon fun v =>
    v ∈ (affineSpan ℝ S : Set V3) ∧ ∃ c : ℝ, ∀ w ∈ S, c = dist v w

/-- HOL `radV` (sphere.hl:371): `@c. !w. S w ==> c = dist(circumcenter S,w)`
(the circumradius: distance from the circumcenter; `d/2` for pairs,
`0` for singletons). -/
def radV (S : Set V3) : ℝ :=
  Classical.epsilon fun c => ∀ w ∈ S, c = dist (circumcenter S) w

/-- HOL `rconesgn`-based `rcone_ge` (sphere.hl:454/456): `rconesgn sgn v w h =
{x | sgn ((x-v) dot (w-v)) (dist(x,v)*dist(w,v)*h)}`, here with `≥`. -/
def rconeGe (v w : V3) (h : ℝ) : Set V3 :=
  {x | (x - v) ⬝ᵥ (w - v) ≥ dist x v * dist w v * h}

/-- HOL `rcone_gt` (sphere.hl:454/458), with `>`. -/
def rconeGt (v w : V3) (h : ℝ) : Set V3 :=
  {x | (x - v) ⬝ᵥ (w - v) > dist x v * dist w v * h}

/-- HOL `saturated` (sphere.hl:439; pack1.hl:159). Ported in THIS wave per
docs/packing-manifest.md §3 ("not yet on Lean side — port with pack_defs
wave"); if PackingAuto1 also defines it, keep one copy at merge time. -/
def saturated (V : Set V3) : Prop := ∀ x, ∃ y ∈ V, dist x y < 2

/-- HOL `wedge_ge` (REUHADY.hl:51): `{z | 0 <= azim v0 v1 w1 z /\
azim v0 v1 w1 z <= azim v0 v1 w1 w2}` (the closed wedge; equals
`Kepler.Text.Fan.cwedge`). -/
def wedgeGe (v0 v1 w1 w2 : V3) : Set V3 :=
  {z | 0 ≤ azim v0 v1 w1 z ∧ azim v0 v1 w1 z ≤ azim v0 v1 w1 w2}

/-- HOL `hl` (pack_defs.hl:26): `radV (set_of_list ul)`; half-length for
pairs, circumradius for simplices. -/
def hl (ul : List V3) : ℝ := radV (setOfList ul)

/-- Reconstruction of core-Flyspeck `vor_list` (used only by KHEJKCI_concl;
absent from all local HL sources). Hypothesis strength to be reconciled at
fill-in time. -/
def vorList (V : Set V3) (k : ℕ) (ul : List V3) : Prop :=
  barV V k ul ∧ hl ul < Real.sqrt 2

/-! ## pack_defs.hl: the 51 definitions -/

/-- HOL `negligible_fun_p` (pack_defs.hl:18). NOTE: pack1.hl:329 carries a
duplicate; the pack_defs copy is canonical (merge-time cleanup). -/
def negligibleFunP (f : V3 → ℝ) (S : Set V3) (p : V3) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → setSum (S ∩ Metric.ball p r) f ≤ C * r ^ 2

/-- HOL `negligible_fun_0` (pack_defs.hl:20): `negligible_fun_p f S 0`. -/
def negligibleFun0 (f : V3 → ℝ) (S : Set V3) : Prop := negligibleFunP f S 0

/-- HOL `fcc_compatible` (pack_defs.hl:22). NOTE: pack1.hl:332 carries a
duplicate; the pack_defs copy is canonical. -/
def fccCompatible (f : V3 → ℝ) (S : Set V3) : Prop :=
  ∀ v ∈ S, Real.sqrt 32 ≤ volume.real (voronoiOpen S v) + f v

/-- HOL `kepler_conjecture` (pack_defs.hl:24). -/
def keplerConjecture : Prop :=
  ∀ V : Set V3, Packing V ∧ saturated V →
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      volume.real (((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 r : Set V3)) /
        volume.real (Metric.ball (0 : V3) r) ≤ Real.pi / Real.sqrt 18 + c / r

/-- HOL `mxi` (pack_defs.hl:39-44): the point at distance `sqrt 2` from
`HD ul` on the segment joining `omega_list_n V ul 2` and `omega_list_n V ul 3`
(chosen by `@` when `hl (truncate_simplex 2 ul) < sqrt 2`). -/
def mxi (V : Set V3) (ul : List V3) : V3 :=
  if Real.sqrt 2 ≤ hl (truncateSimplex 2 ul) then omegaListN V ul 2
  else
    Classical.epsilon fun p =>
      p ∈ convexHull ℝ {omegaListN V ul 2, omegaListN V ul 3} ∧
        dist p (hdV ul) = Real.sqrt 2

/-- HOL `mcell0` (pack_defs.hl:46-47): `rogers V ul DIFF ball(HD ul, sqrt 2)`
— the part of the Rogers simplex outside the `sqrt 2`-ball around its first
vertex (the "radial" annular sliver). -/
def mcell0 (V : Set V3) (ul : List V3) : Set V3 :=
  rogers V ul \ Metric.ball (hdV ul) (Real.sqrt 2)

/-- HOL `mcell1` (pack_defs.hl:49-55): for `sqrt 2 <= hl ul`, the Rogers
simplex inside `cball(HD ul, sqrt 2)` minus the strict radial cone towards
`HD (TL ul)` scaled by `hl (truncate_simplex 1 ul)/sqrt 2`; empty otherwise. -/
def mcell1 (V : Set V3) (ul : List V3) : Set V3 :=
  if Real.sqrt 2 ≤ hl ul then
    (rogers V ul ∩ Metric.closedBall (hdV ul) (Real.sqrt 2)) \
      rconeGt (hdV ul) (hdV ul.tail) (hl (truncateSimplex 1 ul) / Real.sqrt 2)
  else ∅

/-- HOL `mcell2` (pack_defs.hl:57-64): for `hl (truncate_simplex 1 ul) < sqrt 2`
and `sqrt 2 <= hl ul`, the edge cell along `{HD ul, HD (TL ul)}` cut by the two
mutual `rcone_ge`s at `a = hl (truncate_simplex 1 ul)/sqrt 2` and the wedge
`aff_ge {HD ul, HD (TL ul)} {mxi V ul, omega_list_n V ul 3}`; empty otherwise. -/
def mcell2 (V : Set V3) (ul : List V3) : Set V3 :=
  if hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul then
    let a := hl (truncateSimplex 1 ul) / Real.sqrt 2
    (rconeGe (hdV ul) (hdV ul.tail) a ∩ rconeGe (hdV ul.tail) (hdV ul) a) ∩
      affGe {hdV ul, hdV ul.tail} {mxi V ul, omegaListN V ul 3}
  else ∅

/-- HOL `mcell3` (pack_defs.hl:66-69): for `hl (truncate_simplex 2 ul) < sqrt 2`
and `sqrt 2 <= hl ul`, the convex hull of the first three points together with
`mxi V ul`; empty otherwise. -/
def mcell3 (V : Set V3) (ul : List V3) : Set V3 :=
  if hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul then
    convexHull ℝ (setOfList (truncateSimplex 2 ul) ∪ {mxi V ul})
  else ∅

/-- HOL `mcell4` (pack_defs.hl:71-74): for `hl ul < sqrt 2`, the convex hull
of all four points (the Delaunay tetrahedron itself); empty otherwise. -/
def mcell4 (V : Set V3) (ul : List V3) : Set V3 :=
  if hl ul < Real.sqrt 2 then convexHull ℝ (setOfList ul) else ∅

/-- HOL `mcell` (pack_defs.hl:76-78): dispatch on `i` (anything `> 3` gives
`mcell4`). -/
def mcell (i : ℕ) (V : Set V3) (ul : List V3) : Set V3 :=
  if i = 0 then mcell0 V ul
  else if i = 1 then mcell1 V ul
  else if i = 2 then mcell2 V ul
  else if i = 3 then mcell3 V ul
  else mcell4 V ul

/-- HOL `mcell_set` (pack_defs.hl:80-81): all Marchal cells over `barV V 3`
lists. -/
def mcellSet (V : Set V3) : Set (Set V3) :=
  {X | ∃ i ul, X = mcell i V ul ∧ barV V 3 ul}

/-- HOL `cell_params` (pack_defs.hl:84-85): `@(k,ul). k <= 4 /\ ul IN barV V 3
/\ X = mcell k V ul`. -/
def cellParams (V : Set V3) (X : Set V3) : ℕ × List V3 :=
  Classical.epsilon fun p => p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2

/-- HOL `VX` (pack_defs.hl:87-94): the vertices of cell `X` — the first
`k` points of the parameter list (empty for null cells and `k = 0`). -/
def VX (V : Set V3) (X : Set V3) : Set V3 :=
  if nullSet X then ∅
  else
    let p := cellParams V X
    if p.1 = 0 then ∅ else setOfList (truncateSimplex (p.1 - 1) p.2)

/-- HOL `edgeX` (pack_defs.hl:96): `{ {u,v} | VX V X u /\ VX V X v /\ u ≠ v }`. -/
def edgeX (V : Set V3) (X : Set V3) : Set (Set V3) :=
  {e | ∃ u v : V3, e = {u, v} ∧ u ∈ VX V X ∧ v ∈ VX V X ∧ u ≠ v}

/-- HOL `total_solid` (pack_defs.hl:98): `sum (VX V X) (\x. sol x X)`. -/
def totalSolid (V : Set V3) (X : Set V3) : ℝ := setSum (VX V X) fun x => sol x X

/-- HOL `dihu2` (pack_defs.hl:106-107): the dihedral across edge `{u0,u1}`
at the `mxi` level. -/
def dihu2 (V : Set V3) (ul : List V3) : ℝ :=
  dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3)

/-- HOL `dihu3` (pack_defs.hl:109-110): the dihedral across edge `{u0,u1}`
between `EL 2 ul` and `mxi`. -/
def dihu3 (V : Set V3) (ul : List V3) : ℝ :=
  dihV (elV ul 0) (elV ul 1) (elV ul 2) (mxi V ul)

/-- HOL `dihu4` (pack_defs.hl:112-113): the plain tetrahedral dihedral. -/
def dihu4 (ul : List V3) : ℝ :=
  dihV (elV ul 0) (elV ul 1) (elV ul 2) (elV ul 3)

/-- HOL `cell_params_d` (pack_defs.hl:115-117): like `cell_params` but the
witness list must also have `vl` as an initial sublist. -/
def cellParamsD (V : Set V3) (X : Set V3) (vl : List V3) : ℕ × List V3 :=
  Classical.epsilon fun p =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧ initialSublist vl p.2

/-- HOL `dihX` (pack_defs.hl:119-125): the dihedral angle of cell `X` across
the oriented edge `(v0, v1)`, read off from `cell_params_d` at `k = 2,3,4`
(`0` for null cells and `k ≤ 1`). -/
def dihX (V : Set V3) (X : Set V3) (p : V3 × V3) : ℝ :=
  if nullSet X then 0
  else
    let q := cellParamsD V X [p.1, p.2]
    if q.1 = 2 then dihu2 V q.2
    else if q.1 = 3 then dihu3 V q.2
    else if q.1 = 4 then dihu4 q.2
    else 0

/-- HOL `sol0` (pack_defs.hl:128): the regular-tetrahedron solid angle. -/
def sol0 : ℝ := 3 * Real.arccos (1 / 3) - Real.pi

/-- HOL `tau0` (pack_defs.hl:129). -/
def tau0 : ℝ := 4 * Real.pi - 20 * sol0

/-- HOL `mm1` (pack_defs.hl:130). -/
def mm1 : ℝ := sol0 * Real.sqrt 8 / tau0

/-- HOL `mm2` (pack_defs.hl:131). -/
def mm2 : ℝ := (6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0)

/-- HOL `hplus` (pack_defs.hl:132). -/
def hplus : ℝ := 1.3254

/-- HOL `marchal_quartic` (sphere.hl:519; the commented draft at
pack_defs.hl:134-138 differs — this ACTIVE version is ported). -/
def marchalQuartic (h : ℝ) : ℝ :=
  (Real.sqrt 2 - h) * (h - hplus) * (9 * h ^ 2 - 17 * h + 3) /
    ((Real.sqrt 2 - 1) * 5 * (hplus - 1))

/-- HOL `marchal` (pack_defs.hl:140-141): `marchal_quartic` below `sqrt 2`,
else 0. -/
def marchal (h : ℝ) : ℝ := if h ≤ Real.sqrt 2 then marchalQuartic h else 0

/-- HOL `gammaX` (pack_defs.hl:143-145): the weighted cell deficit
`vol X - (2 mm1/pi) total_solid + (8 mm2/pi) sum over edges`. The HL
pattern-lambda `\{u,v}. ...` is rendered by `Classical.epsilon` on the
unfolding `e = {u,v}` (HOL's own pattern abstraction is a choice; the
chapter proves the value order-independent). -/
def gammaX (V : Set V3) (X : Set V3) (f : ℝ → ℝ) : ℝ :=
  volume.real X - (2 * mm1 / Real.pi) * totalSolid V X +
    (8 * mm2 / Real.pi) *
      setSum (edgeX V X) fun e =>
        if e ∈ edgeX V X then
          let q := Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}
          dihX V X (q.1, q.2) * f (hl [q.1, q.2])
        else 0

/-- HOL `h0` (pack_defs.hl:147). -/
def h0 : ℝ := 1.26

/-- HOL `lfun` (pack_defs.hl:149). -/
def lfun (h : ℝ) : ℝ := (h0 - h) / (h0 - 1)

/-- HOL `lmfun` (pack_defs.hl:151): `lfun` cut off at `h0`. -/
def lmfun (h : ℝ) : ℝ := if h ≤ h0 then (h0 - h) / (h0 - 1) else 0

/-- HOL `hminus` (pack_defs.hl:153): `@x. 1.2 <= x /\ x < 1.3 /\
marchal_quartic x = lmfun x`. -/
def hminus : ℝ :=
  Classical.epsilon fun x => 1.2 ≤ x ∧ x < 1.3 ∧ marchalQuartic x = lmfun x

/-- HOL `critical_edgeX` (pack_defs.hl:155-157): edges with length in
`[hminus, hplus]`. -/
def criticalEdgeX (V : Set V3) (X : Set V3) : Set (Set V3) :=
  {e | ∃ u v : V3, e = {u, v} ∧ e ∈ edgeX V X ∧
    hminus ≤ hl [u, v] ∧ hl [u, v] ≤ hplus}

/-- HOL `subcritical_edgeX` (pack_defs.hl:159-160): edges shorter than
`hminus`. -/
def subcriticalEdgeX (V : Set V3) (X : Set V3) : Set (Set V3) :=
  {e | ∃ u v : V3, e = {u, v} ∧ e ∈ edgeX V X ∧ hl [u, v] < hminus}

/-- HOL `critical_weight` (pack_defs.hl:162-163): `1/CARD(critical_edgeX)`. -/
def criticalWeight (V : Set V3) (X : Set V3) : ℝ :=
  1 / (Nat.card (criticalEdgeX V X) : ℝ)

/-- HOL `bump` (pack_defs.hl:165). -/
def bump (h : ℝ) : ℝ :=
  0.005 * (1 - (h - h0) ^ 2 / (hplus - h0) ^ 2)

/-- HOL `critical_edge_y` (pack_defs.hl:167). -/
def criticalEdgeY (y : ℝ) : Prop := 2 * hminus ≤ y ∧ y ≤ 2 * hplus

/-- HOL `wtcount3_y` (pack_defs.hl:169-172). -/
def wtcount3Y (y1 y2 y3 : ℝ) : ℕ :=
  (if criticalEdgeY y1 then 1 else 0) +
    (if criticalEdgeY y2 then 1 else 0) +
    (if criticalEdgeY y3 then 1 else 0)

/-- HOL `wtcount6_y` (pack_defs.hl:174-175). -/
def wtcount6Y (y1 y2 y3 y4 y5 y6 : ℝ) : ℕ :=
  wtcount3Y y1 y2 y3 + wtcount3Y y4 y5 y6

/-- HOL `cell_cluster` (pack_defs.hl:177-178): all cells having `e` as a
critical edge. -/
def cellCluster (V : Set V3) (e : Set V3) : Set (Set V3) :=
  {X | e ∈ criticalEdgeX V X ∧ X ∈ mcellSet V}

/-- HOL `beta_bump_v1` (pack_defs.hl:180-187): the bump correction
`bump (radV e) - bump (radV e')` on the critical-edge pair `(e, e')` of a
cell whose other edges are subcritical. -/
def betaBumpV1 (V : Set V3) (e : Set V3) (X : Set V3) : ℝ :=
  let e' := VX V X \ e
  if X ∈ mcellSet V ∧ ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧
      e' ∈ criticalEdgeX V X ∧
      ∀ f ∈ edgeX V X, f = e ∨ f = e' ∨ f ∈ subcriticalEdgeX V X then
    bump (radV e) - bump (radV e')
  else 0

/-- HOL `cluster_gamma` (pack_defs.hl:189-190). -/
def clusterGamma (V : Set V3) (e : Set V3) (Z : Set (Set V3)) : ℝ :=
  setSum Z fun X => gammaX V X lmfun * criticalWeight V X + betaBumpV1 V e X

/-- HOL `cell_cluster_inequality` (pack_defs.hl:192-193). -/
def cellClusterInequality (V : Set V3) : Prop :=
  ∀ e : Set V3, 0 ≤ clusterGamma V e (cellCluster V e)

/-- HOL `lmfun_inequality` (pack_defs.hl:195-197). -/
def lmfunInequality (V : Set V3) : Prop :=
  ∀ u ∈ V, setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
      (fun v => lmfun (hl [u, v])) ≤ 12

/-- HOL `ball_annulus` (pack_defs.hl:199-200). -/
def ballAnnulus : Set V3 := Metric.closedBall 0 (2 * h0) \ Metric.ball 0 2

/-- HOL `local_annulus_inequality` (pack_defs.hl:202-203). -/
def localAnnulusInequality (V : Set V3) : Prop :=
  setSum V (fun v => lmfun (hl [0, v])) ≤ 12

/-- HOL `fan_of_polyhedron` (pack_defs.hl:205-207): the fan pair
`(extreme points, edges)` of a polyhedron; HOL passes the pair, rendered
here as `V3 × Set (Set V3)`. -/
def fanOfPolyhedron (s : Set V3) : Set V3 × Set (Set V3) :=
  ({u | u ∈ Set.extremePoints ℝ s},
    {e | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧ FaceOf (convexHull ℝ {v, w}) s})

/-! ## GLTVHUM 装配波（GIANT ⑤）: chain-copied kit

PA2 不能 import PA5/PA6（成环），故把 `GLTVHUM_lemma1`（PA6:869，真证）证明体
传递闭包内的 PA5/PA6 件按最小触达集链复制至此；全部 `p2g_` 前缀防撞，
各件注明"PA5/PA6 正本落地，本为链复制"。仅 5 枚上游 sorry 件以桩保留
（`-- NEEDS:` 记账），其余均为真证移植。 -/

/-! ### §0 initialSublist / truncate kit（PA5 链复制） -/

/-- pack3.hl:55 `discrete`. PA5 正本落地，本为链复制。 -/
private def p2gDiscrete (S : Set V3) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∀ x y : V3, x ∈ S → y ∈ S → dist x y < e → x = y

/-- pack3.hl:992 `INITIAL_SUBLIST_APPEND`. PA5 正本落地，本为链复制。 -/
private theorem p2g_INITIAL_SUBLIST_APPEND (ul vl : List V3) :
    initialSublist ul (ul ++ vl) := ⟨vl, rfl⟩

/-- pack3.hl:1022 `INITIAL_SUBLIST_UNIQUE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_INITIAL_SUBLIST_UNIQUE {xl yl zl : List V3} {n : ℕ}
    (h1 : initialSublist xl zl) (h2 : initialSublist yl zl)
    (hl1 : xl.length = n) (hl2 : yl.length = n) : xl = yl := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  have heq : xl ++ t1 = yl ++ t2 := by rw [← ht1, ht2]
  rcases List.append_eq_append_iff.1 heq with ⟨t, rfl, -⟩ | ⟨t, rfl, -⟩
  · rw [List.length_append, hl1] at hl2
    have ht0 : t.length = 0 := by omega
    rw [List.length_eq_zero_iff.1 ht0, List.append_nil]
  · rw [List.length_append, hl2] at hl1
    have ht0 : t.length = 0 := by omega
    rw [List.length_eq_zero_iff.1 ht0, List.append_nil]

/-- pack3.hl:1044 `INITIAL_SUBLIST_TRANS`. PA5 正本落地，本为链复制。 -/
private theorem p2g_INITIAL_SUBLIST_TRANS {xl yl zl : List V3}
    (h1 : initialSublist xl yl) (h2 : initialSublist yl zl) :
    initialSublist xl zl := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  exact ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩

/-- pack3.hl:1051 `INITIAL_SUBLIST_REFL`. PA5 正本落地，本为链复制。 -/
private theorem p2g_INITIAL_SUBLIST_REFL (ul : List V3) :
    initialSublist ul ul := ⟨[], by simp⟩

/-- pack3.hl:1108 `INITIAL_SUBLIST_LENGTH_LE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_INITIAL_SUBLIST_LENGTH_LE {xl zl : List V3}
    (h : initialSublist xl zl) : xl.length ≤ zl.length := by
  obtain ⟨yl, hyl⟩ := h
  rw [hyl, List.length_append]
  omega

/-- pack3.hl:1235 `INITIAL_SUBLIST_HD`. PA5 正本落地，本为链复制。 -/
private theorem p2g_INITIAL_SUBLIST_HD (ul : List V3) (h : 1 ≤ ul.length) :
    initialSublist [hdV ul] ul := by
  cases ul with
  | nil => simp at h
  | cons a t => exact ⟨t, rfl⟩

/-- pack3.hl:1303 `SET_OF_LIST_INITIAL_SUBLIST_SUBSET`. PA5 正本落地，本为链复制。 -/
private theorem p2g_SET_OF_LIST_INITIAL_SUBLIST_SUBSET {vl ul : List V3}
    (h : initialSublist vl ul) : setOfList vl ⊆ setOfList ul := by
  obtain ⟨t, ht⟩ := h
  intro x hx
  rw [ht]
  exact List.mem_append.2 (Or.inl hx)

/-- `truncate_simplex` 的 ε-选取属性（PA5:1113 私件 `trunc_init_len`）。
PA5 正本落地，本为链复制。 -/
private theorem p2g_trunc_init_len (k : ℕ) (zl : List V3) (h : k + 1 ≤ zl.length) :
    initialSublist (truncateSimplex k zl) zl ∧ (truncateSimplex k zl).length = k + 1 := by
  have heps := @Classical.epsilon_spec _
    (fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
    ⟨zl.take (k + 1), List.length_take_of_le (by omega),
      ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
  exact ⟨heps.2, heps.1⟩

/-- pack3.hl:1760 `TRUNCATE_SIMPLEX_INITIAL_SUBLIST`. PA5 正本落地，本为链复制。 -/
private theorem p2g_TRUNCATE_SIMPLEX_INITIAL_SUBLIST (k : ℕ) (xl zl : List V3) :
    (truncateSimplex k zl = xl ∧ k + 1 ≤ zl.length) ↔
      initialSublist xl zl ∧ xl.length = k + 1 := by
  constructor
  · rintro ⟨heps, hle⟩
    have hw : (truncateSimplex k zl).length = k + 1 ∧
        initialSublist (truncateSimplex k zl) zl :=
      Classical.epsilon_spec
        (p := fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
        ⟨zl.take (k + 1), List.length_take_of_le (by omega),
          ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
    rw [heps] at hw
    exact ⟨hw.2, hw.1⟩
  · rintro ⟨hinit, hlen⟩
    have hle2 := p2g_INITIAL_SUBLIST_LENGTH_LE hinit
    have hw : (truncateSimplex k zl).length = k + 1 ∧
        initialSublist (truncateSimplex k zl) zl :=
      Classical.epsilon_spec
        (p := fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
        ⟨zl.take (k + 1), List.length_take_of_le (by omega),
          ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
    refine ⟨(p2g_INITIAL_SUBLIST_UNIQUE hinit hw.2 hlen hw.1).symm, by omega⟩

/-- 辅助：`barV` 对 initial sublist 下降（PA5:1134 `BARV_INITIAL_SUBLIST`）。原
PA5 证明引用的是 barV 的第二条——此处按同法重证。PA5 正本落地，本为链复制。 -/
private theorem barV_of_initialSublist_p2 (V : Set V3) (k : ℕ) (ul : List V3) (vl : List V3)
    (hbar : barV V k ul) (hsub : initialSublist vl ul) (hpos : 0 < vl.length) :
    barV V (vl.length - 1) vl := by
  refine ⟨by omega, fun wl hwl => hbar.2 wl ⟨p2g_INITIAL_SUBLIST_TRANS hwl.1 hsub, hwl.2⟩⟩

/-- pack3.hl:1777 `TRUNCATE_SIMPLEX_BARV`. PA5 正本落地，本为链复制。 -/
private theorem p2g_TRUNCATE_SIMPLEX_BARV (V : Set V3) (r k : ℕ) (zl : List V3)
    (hbar : barV V k zl) (hr : r ≤ k) : barV V r (truncateSimplex r zl) := by
  have hbl := hbar.1
  have h1 := p2g_trunc_init_len r zl (by omega)
  have hb := barV_of_initialSublist_p2 V k zl (truncateSimplex r zl) hbar h1.1 (by omega)
  rw [h1.2] at hb
  simpa using hb

/-- pack3.hl:1792 `TRUNCATE_SIMPLEX_REFL`. PA5 正本落地，本为链复制。 -/
private theorem p2g_TRUNCATE_SIMPLEX_REFL (k : ℕ) (ul : List V3) (h : ul.length = k + 1) :
    truncateSimplex k ul = ul := by
  have heps : (truncateSimplex k ul).length = k + 1 ∧ initialSublist (truncateSimplex k ul) ul :=
    Classical.epsilon_spec (p := fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl ul)
      ⟨ul, h, p2g_INITIAL_SUBLIST_REFL ul⟩
  exact p2g_INITIAL_SUBLIST_UNIQUE heps.2 (p2g_INITIAL_SUBLIST_REFL ul) heps.1 h

/-- pack3.hl:1799 `TRUNCATE_0_EQ_HEAD`. PA5 正本落地，本为链复制。 -/
private theorem p2g_TRUNCATE_0_EQ_HEAD (ul : List V3) (h : 1 ≤ ul.length) :
    truncateSimplex 0 ul = [hdV ul] := by
  have hw : (truncateSimplex 0 ul).length = 0 + 1 ∧
      initialSublist (truncateSimplex 0 ul) ul :=
    Classical.epsilon_spec (p := fun vl : List V3 => vl.length = 0 + 1 ∧ initialSublist vl ul)
      ⟨[hdV ul], rfl, p2g_INITIAL_SUBLIST_HD ul h⟩
  have h1 := p2g_trunc_init_len 0 ul h
  exact p2g_INITIAL_SUBLIST_UNIQUE h1.1 (p2g_INITIAL_SUBLIST_HD ul h) hw.1 rfl

/-- pack3.hl:1814 `TRUNCATE_SIMPLEX_EQ_BUTLAST` 不需要；`TRUNCATE_TRUNCATE_SIMPLEX`
（pack3.hl:1831）。PA5 正本落地，本为链复制。 -/
private theorem p2g_TRUNCATE_TRUNCATE_SIMPLEX (ul : List V3) (i j : ℕ) (hij : i ≤ j)
    (h : j + 1 ≤ ul.length) :
    truncateSimplex i (truncateSimplex j ul) = truncateSimplex i ul := by
  have hB := p2g_trunc_init_len j ul h
  have hlen : i + 1 ≤ (truncateSimplex j ul).length := by omega
  have hA := p2g_trunc_init_len i (truncateSimplex j ul) hlen
  have hC := p2g_trunc_init_len i ul (by omega)
  exact p2g_INITIAL_SUBLIST_UNIQUE (p2g_INITIAL_SUBLIST_TRANS hA.1 hB.1) hC.1 hA.2 hC.2

/-- pack3.hl:1822 `HD_TRUNCATE_SIMPLEX`. PA5 正本落地，本为链复制。 -/
private theorem p2g_HD_TRUNCATE_SIMPLEX (ul : List V3) (j : ℕ) (h : j + 1 ≤ ul.length) :
    hdV (truncateSimplex j ul) = hdV ul := by
  have h1 := p2g_trunc_init_len j ul h
  obtain ⟨yl, hyl⟩ := h1.1
  cases ul with
  | nil => exact absurd h (by simp [List.length_nil])
  | cons a t =>
    cases hs : truncateSimplex j (a :: t) with
    | nil =>
      rw [hs] at h1
      rw [List.length_nil] at h1
      exact absurd h1.2 (by omega)
    | cons b s =>
      rw [hs] at hyl
      injection hyl with e1 _
      simp only [hdV]
      exact e1.symm

/-- pack3.hl:1686 `BARV_SUBSET`. PA5 正本落地，本为链复制。 -/
private theorem p2g_BARV_SUBSET (V : Set V3) (k : ℕ) (ul : List V3) (hbar : barV V k ul) :
    setOfList ul ⊆ V :=
      (hbar.2 ul ⟨p2g_INITIAL_SUBLIST_REFL ul, by simp [hbar.1]⟩).2.1

/-- pack3.hl:1702 `BARV_CONS`. PA5 正本落地，本为链复制。 -/
private theorem p2g_BARV_CONS (V : Set V3) (k : ℕ) (ul : List V3) (hbar : barV V k ul) :
    ∃ hd : V3, ∃ tl : List V3, ul = hd :: tl ∧ hd = hdV ul := by
  cases ul with
  | nil => exact absurd hbar.1 (by simp)
  | cons a t => exact ⟨a, t, rfl, rfl⟩

/-- pack3.hl:1740 `BARV_IMP_K_LE_3`. PA5 正本落地，本为链复制。 -/
private theorem p2g_BARV_IMP_K_LE_3 (V : Set V3) (ul : List V3) (k : ℕ)
    (hbar : barV V k ul) : k ≤ 3 := by
  have h1 := hbar.2 ul ⟨p2g_INITIAL_SUBLIST_REFL ul, by simp [hbar.1]⟩
  have h2 := h1.1
  have h3 := hbar.1
  omega

/-! ### §1 bisector kit（PA5 链复制；`bis` 用 PA2 私件正本） -/

/-- 桥助：dotProduct 左线性（PA5 私件 `dsub_dot`）。PA5 正本落地，本为链复制。 -/
private theorem p2g_dsub_dot (a b z : V3) : (a - b) ⬝ᵥ z = a ⬝ᵥ z - b ⬝ᵥ z := by
  rw [← inner_eq_dot (a - b) z, inner_sub_left, inner_eq_dot a z, inner_eq_dot b z]

/-- 桥助：bisector 归属的 dot 形（PA5 私件 `bis_mem_eq`）。PA5 正本落地，本为链复制。 -/
private theorem p2g_bis_mem_eq (u v x : V3) :
    x ∈ bis u v ↔ 2 * ((v - u) ⬝ᵥ x) = v ⬝ᵥ v - u ⬝ᵥ u := by
  have hnorm : ∀ w : V3, ‖w‖ ^ 2 = w ⬝ᵥ w := by
    intro w
    rw [← inner_eq_dot w w, real_inner_self_eq_norm_sq]
  have key : ∀ w : V3, ‖x - w‖ ^ 2 = ‖x‖ ^ 2 - 2 * (w ⬝ᵥ x) + w ⬝ᵥ w := by
    intro w
    have h1 := norm_sub_sq_real (x := x) (y := w)
    rw [← real_inner_comm x w, inner_eq_dot w x, hnorm w] at h1
    linarith
  simp only [bis, Set.mem_setOf_eq, dist_eq_norm]
  constructor
  · intro h
    have h2 : ‖x - u‖ ^ 2 = ‖x - v‖ ^ 2 := by rw [h]
    have h3 := key u
    have h4 := key v
    rw [p2g_dsub_dot]
    linarith
  · intro h
    rw [p2g_dsub_dot] at h
    have h2 : ‖x - u‖ ^ 2 = ‖x - v‖ ^ 2 := by
      have h3 := key u
      have h4 := key v
      linarith
    have e1 : Real.sqrt (‖x - u‖ ^ 2) = ‖x - u‖ := Real.sqrt_sq (norm_nonneg _)
    have e2 : Real.sqrt (‖x - v‖ ^ 2) = ‖x - v‖ := Real.sqrt_sq (norm_nonneg _)
    have h4 : Real.sqrt (‖x - u‖ ^ 2) = Real.sqrt (‖x - v‖ ^ 2) := by rw [h2]
    rw [e1, e2] at h4
    exact h4

/-- 桥助：`bis_le` 归属的 dot 形（PA5 私件 `bis_mem_le`）。PA5 正本落地，本为链复制。 -/
private theorem p2g_bis_mem_le (u v x : V3) :
    x ∈ bisLe u v ↔ 2 * ((v - u) ⬝ᵥ x) ≤ v ⬝ᵥ v - u ⬝ᵥ u := by
  have hnorm : ∀ w : V3, ‖w‖ ^ 2 = w ⬝ᵥ w := by
    intro w
    rw [← inner_eq_dot w w, real_inner_self_eq_norm_sq]
  have key : ∀ w : V3, ‖x - w‖ ^ 2 = ‖x‖ ^ 2 - 2 * (w ⬝ᵥ x) + w ⬝ᵥ w := by
    intro w
    have h1 := norm_sub_sq_real (x := x) (y := w)
    rw [← real_inner_comm x w, inner_eq_dot w x, hnorm w] at h1
    linarith
  simp only [bisLe, Set.mem_setOf_eq, dist_eq_norm]
  constructor
  · intro h
    have h2 : ‖x - u‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
      have hnu : 0 ≤ ‖x - u‖ := norm_nonneg _
      have hnv : 0 ≤ ‖x - v‖ := norm_nonneg _
      calc ‖x - u‖ ^ 2 = ‖x - u‖ * ‖x - u‖ := sq _
        _ ≤ ‖x - v‖ * ‖x - u‖ := by nlinarith
        _ ≤ ‖x - v‖ * ‖x - v‖ := by nlinarith
        _ = ‖x - v‖ ^ 2 := (sq _).symm
    have h3 := key u
    have h4 := key v
    rw [p2g_dsub_dot]
    linarith
  · intro h
    rw [p2g_dsub_dot] at h
    have h2 : ‖x - u‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
      have h3 := key u
      have h4 := key v
      linarith
    calc ‖x - u‖ = Real.sqrt (‖x - u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖x - v‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖x - v‖ := Real.sqrt_sq (norm_nonneg _)

/-- pack3.hl:34 `BIS_SYM`. PA5 正本落地，本为链复制。 -/
private theorem p2g_BIS_SYM (p q : V3) : bis p q = bis q p :=
  Set.ext fun _ => eq_comm

/-- pack3.hl:385 `BIS_EQ_HYPERPLANE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_BIS_EQ_HYPERPLANE (u v : V3) :
    bis u v = {x : V3 | 2 * ((v - u) ⬝ᵥ x) = v ⬝ᵥ v - u ⬝ᵥ u} :=
  Set.ext (p2g_bis_mem_eq u v)

/-- pack3.hl:391 `BIS_LE_EQ_HALFSPACE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_BIS_LE_EQ_HALFSPACE (u v : V3) :
    bisLe u v = {x : V3 | 2 * ((v - u) ⬝ᵥ x) ≤ v ⬝ᵥ v - u ⬝ᵥ u} :=
  Set.ext (p2g_bis_mem_le u v)

/-- pack3.hl:397 `CONVEX_BIS_LE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CONVEX_BIS_LE (u v : V3) : Convex ℝ (bisLe u v) := by
  intro x hx y hy a b ha hb hab
  rw [p2g_BIS_LE_EQ_HALFSPACE] at hx hy ⊢
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [← inner_eq_dot (v - u) (a • x + b • y), inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_eq_dot (v - u) x, inner_eq_dot (v - u) y]
  have h1 : 2 * (a * ((v - u) ⬝ᵥ x)) ≤ a * (v ⬝ᵥ v - u ⬝ᵥ u) := by
    rw [show 2 * (a * ((v - u) ⬝ᵥ x)) = a * (2 * ((v - u) ⬝ᵥ x)) from by ring]
    exact mul_le_mul_of_nonneg_left hx ha
  have h2 : 2 * (b * ((v - u) ⬝ᵥ y)) ≤ b * (v ⬝ᵥ v - u ⬝ᵥ u) := by
    rw [show 2 * (b * ((v - u) ⬝ᵥ y)) = b * (2 * ((v - u) ⬝ᵥ y)) from by ring]
    exact mul_le_mul_of_nonneg_left hy hb
  have h5 : a * (v ⬝ᵥ v - u ⬝ᵥ u) + b * (v ⬝ᵥ v - u ⬝ᵥ u) = v ⬝ᵥ v - u ⬝ᵥ u := by
    rw [← add_mul, hab, one_mul]
  rw [mul_add]
  linarith

/-- pack3.hl:402 `CLOSED_BIS_LE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CLOSED_BIS_LE (u v : V3) : IsClosed (bisLe u v) := by
  have hc : Continuous fun x : V3 => (v - u) ⬝ᵥ x := by
    have h2 : Continuous fun t : V3 => inner ℝ (v - u) t :=
      continuous_const.inner continuous_id
    simpa [inner_eq_dot] using h2
  rw [p2g_BIS_LE_EQ_HALFSPACE]
  exact isClosed_le (continuous_const.mul hc) continuous_const

/-- pack3.hl:406 `CONVEX_BIS`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CONVEX_BIS (u v : V3) : Convex ℝ (bis u v) := by
  have h : bis u v = bisLe u v ∩ bisLe v u := by
    ext x
    simp only [bis, bisLe, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h1
      exact ⟨le_of_eq h1, le_of_eq h1.symm⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
  rw [h]
  exact (p2g_CONVEX_BIS_LE u v).inter (p2g_CONVEX_BIS_LE v u)

/-- Rogers.hl:35 `BIS_FACE_OF_BIS_LE`（PA6 正本）。PA6 正本落地，本为链复制。 -/
private theorem p2g_BIS_FACE_OF_BIS_LE (u v : V3) : FaceOf (bis u v) (bisLe u v) := by
  refine ⟨fun x hx => by simpa only [bisLe, Set.mem_setOf_eq] using le_of_eq hx,
    p2g_CONVEX_BIS u v, ?_⟩
  intro a b x ha hb hx hseg
  rw [p2g_BIS_EQ_HYPERPLANE] at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [p2g_BIS_LE_EQ_HALFSPACE] at ha hb
  simp only [Set.mem_setOf_eq] at ha hb
  simp only [openSegment, Set.mem_setOf_eq] at hseg
  obtain ⟨t1, t2, ht1, ht2, ht12, hxt⟩ := hseg
  -- linearity of `z ↦ (v - u) ⬝ᵥ z` along the segment
  have hsmul : ∀ (r : ℝ) (y : V3), (v - u) ⬝ᵥ (r • y) = r * ((v - u) ⬝ᵥ y) :=
    fun r y => dotProduct_smul r ((v - u : V3) : Fin 3 → ℝ) (y : Fin 3 → ℝ)
  have hadd : ∀ (y z : V3), (v - u) ⬝ᵥ (y + z) =
      (v - u) ⬝ᵥ y + (v - u) ⬝ᵥ z :=
    fun y z => dotProduct_add ((v - u : V3) : Fin 3 → ℝ) (y : Fin 3 → ℝ)
      (z : Fin 3 → ℝ)
  set A := 2 * ((v - u) ⬝ᵥ a) with hAdef
  set B := 2 * ((v - u) ⬝ᵥ b) with hBdef
  set C := v ⬝ᵥ v - u ⬝ᵥ u with hCdef
  have h1 : t1 * A + t2 * B = C := by
    rw [← hx, ← hxt, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul,
      hadd, hsmul, hsmul]
    ring
  have h2 : t1 * C + t2 * C = C := by rw [← add_mul, ht12, one_mul]
  have hz1 : t1 * (C - A) + t2 * (C - B) = 0 := by nlinarith
  have hz2 : t1 * (C - A) = 0 := by
    have hnn1 : 0 ≤ t1 * (C - A) := mul_nonneg ht1.le (sub_nonneg.2 ha)
    have hnn2 : 0 ≤ t2 * (C - B) := mul_nonneg ht2.le (sub_nonneg.2 hb)
    nlinarith
  have hz3 : t2 * (C - B) = 0 := by
    have hnn1 : 0 ≤ t1 * (C - A) := mul_nonneg ht1.le (sub_nonneg.2 ha)
    have hnn2 : 0 ≤ t2 * (C - B) := mul_nonneg ht2.le (sub_nonneg.2 hb)
    nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-! ### §2 Voronoi 胞 kit（PA5 链复制） -/

/-- pack3.hl:464 `CLOSED_DISCRETE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CLOSED_DISCRETE (A : Set V3) (hA : p2gDiscrete A) : IsClosed A := by
  obtain ⟨e, he, hsep⟩ := hA
  have hsub : closure A ⊆ A := by
    intro x hxc
    by_contra hxA
    obtain ⟨y0, hy0A, hy0d⟩ := Metric.mem_closure_iff.1 hxc (e / 2) (by linarith)
    have hball : ∀ z ∈ A, dist x z < e / 2 → z = y0 := by
      intro z hz hzd
      exact (hsep y0 z hy0A hz (by
        have ht := dist_triangle y0 x z
        rw [dist_comm y0 x] at ht
        linarith)).symm
    have hpos : 0 < dist x y0 := dist_pos.2 fun h => hxA (h ▸ hy0A)
    obtain ⟨z, hzA, hzd⟩ := Metric.mem_closure_iff.1 hxc (dist x y0 / 2) (by positivity)
    have hzlt : dist x z < e / 2 := by linarith
    have hzy := hball z hzA hzlt
    rw [hzy] at hzd
    linarith
  exact closure_subset_iff_isClosed.1 hsub

/-- pack3.hl:536 `PACKING_IMP_DISCRETE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_PACKING_IMP_DISCRETE (V : Set V3) (hV : Packing V) : p2gDiscrete V :=
  ⟨2, two_pos, fun x y hx hy hlt => hV x hx y hy hlt⟩

/-- pack3.hl:613 `CENTER_IN_VORONOI_CELL`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CENTER_IN_VORONOI_CELL (V : Set V3) (v : V3) :
    v ∈ voronoiClosed V v ∧ v ∈ voronoiOpen V v := by
  refine ⟨fun w _ => by rw [dist_self]; exact dist_nonneg, fun w _ hwne => by
    rw [dist_self v]
    exact dist_pos.2 (Ne.symm hwne)⟩

/-- pack3.hl:629 `VORONOI_CLOSED_CONTAINS_BALL`. PA5 正本落地，本为链复制。
（`voronoiOpen` 为 PA2 私件正本。） -/
private theorem p2g_VORONOI_CLOSED_CONTAINS_BALL (V : Set V3) (v : V3) (hV : Packing V) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball v r ⊆ voronoiClosed V v := by
  by_cases hvV : v ∈ V
  · refine ⟨1, one_pos, fun x hx w hw => ?_⟩
    by_cases hvw : w = v
    · subst hvw; exact le_refl _
    · have h2 : 2 ≤ dist v w := by
        have h3 := hV.dist_ge_two hw hvV hvw
        rwa [dist_comm w v] at h3
      have h1 : dist x v < 1 := Metric.mem_ball.1 hx
      have ht := dist_triangle v x w
      rw [dist_comm v x] at ht
      linarith
  · have hVcl : IsClosed V := p2g_CLOSED_DISCRETE V (p2g_PACKING_IMP_DISCRETE V hV)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVcl.isOpen_compl v (by simpa using hvV)
    refine ⟨ε / 4, by linarith, fun x hx u hu => ?_⟩
    have hge : ∀ u ∈ V, ε ≤ dist v u := by
      intro u hu
      refine le_of_not_gt fun hcon => ?_
      have hmem : u ∈ Metric.ball v ε := Metric.mem_ball.2 (by rw [dist_comm]; exact hcon)
      have hc : u ∈ Vᶜ := hball hmem
      rw [Set.mem_compl_iff] at hc
      exact hc hu
    have hxv := Metric.mem_ball.1 hx
    have ht := dist_triangle v x u
    rw [dist_comm v x] at ht
    have hge' := hge u hu
    linarith

/-- 桥：含开球的集满仿射维（PA5 私件 `CONTAINS_BALL_AFFINE_HULL`，真证一行）。
PA5 正本落地，本为链复制。 -/
private theorem p2g_CONTAINS_BALL_AFFINE_HULL (s : Set V3) (x : V3) (r : ℝ) (hr : 0 < r)
    (h : Metric.ball x r ⊆ s) : affineSpan ℝ s = ⊤ :=
  affineSpan_eq_top_of_nonempty_interior
    ⟨x, (interior_maximal
      ((subset_convexHull ℝ (Metric.ball x r)).trans (convexHull_mono h))
      Metric.isOpen_ball) (Metric.mem_ball_self hr)⟩

/-- 桥：含开球 ⇒ affDim = 3（PA5 私件 `affDim_of_mem_ball`）。PA5 正本落地，
本为链复制。 -/
private theorem p2g_affDim_of_mem_ball (s : Set V3) (x : V3) (r : ℝ) (hr : 0 < r)
    (hsub : Metric.ball x r ⊆ s) : affDim s = 3 := by
  have hne : s ≠ ∅ := fun hc => nonempty_iff_ne_empty.1
    ⟨x, hsub (Metric.mem_ball_self hr)⟩ hc
  have htop : affineSpan ℝ s = ⊤ := p2g_CONTAINS_BALL_AFFINE_HULL s x r hr hsub
  have hd : vectorSpan ℝ s = ⊤ := by
    rw [← direction_affineSpan, htop]
    exact AffineSubspace.direction_top _ _ _
  rw [affDim, if_neg hne, hd, finrank_top, finrank_euclideanSpace_fin]
  norm_num

/-- pack3.hl:753 `AFF_DIM_VORONOI_CLOSED`. PA5 正本落地，本为链复制。 -/
private theorem p2g_AFF_DIM_VORONOI_CLOSED (V : Set V3) (v : V3) (hV : Packing V) :
    affDim (voronoiClosed V v) = 3 := by
  obtain ⟨r, hr, hball⟩ := p2g_VORONOI_CLOSED_CONTAINS_BALL V v hV
  exact p2g_affDim_of_mem_ball _ v r hr hball

/-- pack3.hl:789 `VORONOI_CLOSED_EQ_INTERS_BIS_LE`. PA5 正本落地，本为链复制。 -/
private theorem p2g_VORONOI_CLOSED_EQ_INTERS_BIS_LE (S : Set V3) (v : V3) :
    voronoiClosed S v = ⋂₀ ((fun w : V3 => bisLe v w) '' S) := by
  rw [voronoiClosed]
  ext x
  refine ⟨fun h t ht => ?_, fun h w hw => h (bisLe v w) ⟨w, hw, rfl⟩⟩
  obtain ⟨w, hw, heq⟩ := ht
  rw [← heq]
  exact h w hw

/-- pack3.hl:940 `CONVEX_VORONOI_CLOSED`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CONVEX_VORONOI_CLOSED (S : Set V3) (v : V3) :
    Convex ℝ (voronoiClosed S v) := by
  rw [p2g_VORONOI_CLOSED_EQ_INTERS_BIS_LE]
  refine convex_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact p2g_CONVEX_BIS_LE v w

/-- pack3.hl:949 `CLOSED_VORONOI_CLOSED`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CLOSED_VORONOI_CLOSED (S : Set V3) (v : V3) :
    IsClosed (voronoiClosed S v) := by
  rw [p2g_VORONOI_CLOSED_EQ_INTERS_BIS_LE]
  refine isClosed_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact p2g_CLOSED_BIS_LE v w

/-- pack3.hl:1949 `VORONOI_SET_SING`. PA5 正本落地，本为链复制。 -/
private theorem p2g_VORONOI_SET_SING (V : Set V3) (u : V3) :
    voronoiSet V {u} = voronoiClosed V u := by
  ext x
  constructor
  · intro h t ht
    exact h (voronoiClosed V u) ⟨u, rfl, rfl⟩ t ht
  · intro h t ht
    obtain ⟨v, hv, hvt⟩ := ht
    rw [Set.mem_singleton_iff.1 hv] at hvt
    rw [← hvt]
    exact h

/-- pack3.hl:1961 `VORONOI_LIST_SING`. PA5 正本落地，本为链复制。 -/
private theorem p2g_VORONOI_LIST_SING (V : Set V3) (u : V3) :
    voronoiList V [u] = voronoiClosed V u := by
  have hs : setOfList [u] = {u} := by simp [setOfList]
  rw [voronoiList, hs, p2g_VORONOI_SET_SING]

/-- pack3.hl:2115 `VORONOI_LIST_INTER_BIS`. PA5 正本落地，本为链复制。 -/
private theorem p2g_VORONOI_LIST_INTER_BIS (V : Set V3) (ul : List V3) (v : V3) (h : V3)
    (t : List V3) (hsub : setOfList ul ⊆ V) (hv : v ∈ V) (hcons : ul = h :: t) :
    voronoiList V ul ∩ bis h v = voronoiList V (ul ++ [v]) := by
  subst hcons
  have hVh : h ∈ V := hsub (by simp [setOfList])
  ext x
  simp only [Set.mem_inter_iff, bis, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxl, hbis⟩
    intro T hT
    obtain ⟨w, hw, rfl⟩ := hT
    intro z hz
    have hw2 : w ∈ (h :: (t ++ [v]) : List V3) := hw
    rcases List.mem_cons.1 hw2 with heq | hwt
    · rw [heq]
      have hm : h ∈ setOfList (h :: t) := by simp [setOfList]
      exact hxl (voronoiClosed V h) ⟨h, hm, rfl⟩ z hz
    · rcases List.mem_append.1 hwt with hw' | heq2
      · have hm : w ∈ setOfList (h :: t) := by
          simp only [setOfList, List.mem_cons]
          exact Or.inr hw'
        exact hxl (voronoiClosed V w) ⟨w, hm, rfl⟩ z hz
      · rw [List.mem_singleton.1 heq2, ← hbis]
        have hm : h ∈ setOfList (h :: t) := by simp [setOfList]
        exact hxl (voronoiClosed V h) ⟨h, hm, rfl⟩ z hz
  · rintro hxm
    refine ⟨?_, ?_⟩
    · intro T hT
      obtain ⟨w, hw, rfl⟩ := hT
      intro z hz
      have hw2 : w ∈ (h :: t : List V3) := hw
      rcases List.mem_cons.1 hw2 with heq | hw'
      · rw [heq]
        have hm : h ∈ setOfList (h :: (t ++ [v])) := by
          simp only [setOfList, List.mem_cons]
          exact Or.inl rfl
        exact hxm (voronoiClosed V h) ⟨h, hm, rfl⟩ z hz
      · have hm : w ∈ setOfList (h :: (t ++ [v])) := by
          simp only [setOfList, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl hw')
        exact hxm (voronoiClosed V w) ⟨w, hm, rfl⟩ z hz
    · have hm1 : h ∈ setOfList (h :: (t ++ [v])) := by
        simp only [setOfList, List.mem_cons]
        exact Or.inl rfl
      have hm2 : v ∈ setOfList (h :: (t ++ [v])) := by
        simp only [setOfList, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (Or.inl rfl))
      have h1 : dist x h ≤ dist x v := hxm (voronoiClosed V h) ⟨h, hm1, rfl⟩ v hv
      have h2 : dist x v ≤ dist x h := hxm (voronoiClosed V v) ⟨v, hm2, rfl⟩ h hVh
      exact le_antisymm h1 h2

/-- pack3.hl:2380 `CONVEX_VORONOI_LIST`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CONVEX_VORONOI_LIST (V : Set V3) (ul : List V3) :
    Convex ℝ (voronoiList V ul) := by
  rw [voronoiList, voronoiSet]
  refine convex_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact p2g_CONVEX_VORONOI_CLOSED V w

/-- pack3.hl:2370 `CLOSED_VORONOI_LIST`. PA5 正本落地，本为链复制。 -/
private theorem p2g_CLOSED_VORONOI_LIST (V : Set V3) (ul : List V3) :
    IsClosed (voronoiList V ul) := by
  rw [voronoiList, voronoiSet]
  refine isClosed_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact p2g_CLOSED_VORONOI_CLOSED V w

/-! ### §3 omega kit（PA5 三 sorry 件按 HOL pack3.hl:2423/2451/2472 同法在 PA2 重证） -/

/-- pack3.hl:2391 `AFF_DIM_VORONOI_LIST`. PA5 正本落地，本为链复制。 -/
private theorem p2g_AFF_DIM_VORONOI_LIST (V : Set V3) (ul : List V3) (k : ℕ)
    (hbar : barV V k ul) : affDim (voronoiList V ul) = 3 - k := by
  have h1 := hbar.1
  have h3 := (hbar.2 ul ⟨p2g_INITIAL_SUBLIST_REFL ul, by simp [hbar.1]⟩).2.2
  omega

/-- pack3.hl:2451 `BARV_IMP_VORONOI_LIST_NOT_EMPTY`（PA5 正本 sorry；此处重证：
affDim(∅) = -1 与 3 - k ≥ 0 矛盾）。PA5 正本落地后替换。 -/
private theorem p2g_BARV_IMP_VORONOI_LIST_NOT_EMPTY (V : Set V3) (ul : List V3) (k : ℕ)
    (hbar : barV V k ul) : voronoiList V ul ≠ ∅ := by
  intro hc
  have hdim := p2g_AFF_DIM_VORONOI_LIST V ul k hbar
  rw [hc, affDim_empty] at hdim
  have hkle := p2g_BARV_IMP_K_LE_3 V ul k hbar
  omega

/-- pack3.hl:2423 `OMEGA_LIST_N_LEMMA`（PA5 正本 sorry；此处按 HOL 同法重证：
对 k 归纳，用 `TRUNCATE_TRUNCATE_SIMPLEX` 与 `HD_TRUNCATE_SIMPLEX`）。
PA5 正本落地后替换。 -/
private theorem p2g_OMEGA_LIST_N_LEMMA (V : Set V3) (ul : List V3) (k i : ℕ)
    (h : k + i + 1 ≤ ul.length) :
    omegaListN V ul k = omegaListN V (truncateSimplex (k + i) ul) k := by
  induction k generalizing i with
  | zero =>
    simp only [Nat.zero_add]
    exact (p2g_HD_TRUNCATE_SIMPLEX ul i (by omega)).symm
  | succ k ih =>
    have h' : k + (i + 1) + 1 ≤ ul.length := by omega
    have h2 := ih (i + 1) h'
    have hshift : k + (i + 1) = k + 1 + i := by omega
    rw [hshift] at h2
    have htt := p2g_TRUNCATE_TRUNCATE_SIMPLEX ul (k + 1) (k + 1 + i) (by omega) (by omega)
    show closestPoint (voronoiList V (truncateSimplex (k + 1) ul)) (omegaListN V ul k) =
      closestPoint (voronoiList V (truncateSimplex (k + 1) (truncateSimplex (k + 1 + i) ul)))
        (omegaListN V (truncateSimplex (k + 1 + i) ul) k)
    rw [htt, h2]

/-- pack3.hl:2472 `OMEGA_LIST_N_IN_VORONOI_LIST`（PA5 正本 sorry；此处按 HOL 同法
重证：level 0 是头点，步用 Hilbert 投影存在定理
`exists_norm_eq_iInf_of_complete_convex` 于非空闭凸胞）。PA5 正本落地后替换。 -/
private theorem p2g_OMEGA_LIST_N_IN_VORONOI_LIST (V : Set V3) (ul : List V3) (k i : ℕ)
    (hbar : barV V k ul) (hi : i ≤ k) :
    omegaListN V ul i ∈ voronoiList V (truncateSimplex i ul) := by
  have hbl : ul.length = k + 1 := hbar.1
  have hne : ∀ j : ℕ, j ≤ k → (voronoiList V (truncateSimplex j ul)).Nonempty := by
    intro j hj
    exact Set.nonempty_iff_ne_empty.mpr
      (p2g_BARV_IMP_VORONOI_LIST_NOT_EMPTY V (truncateSimplex j ul) j
        (p2g_TRUNCATE_SIMPLEX_BARV V j k ul hbar hj))
  induction i with
  | zero =>
    rw [show omegaListN V ul 0 = hdV ul from rfl, p2g_TRUNCATE_0_EQ_HEAD ul (by omega),
      p2g_VORONOI_LIST_SING]
    exact (p2g_CENTER_IN_VORONOI_CELL V (hdV ul)).1
  | succ n ih =>
    show closestPoint (voronoiList V (truncateSimplex (n + 1) ul))
      (omegaListN V ul n) ∈ voronoiList V (truncateSimplex (n + 1) ul)
    have hKne := hne (n + 1) (by omega)
    have hKconv : Convex ℝ (voronoiList V (truncateSimplex (n + 1) ul)) :=
      p2g_CONVEX_VORONOI_LIST V (truncateSimplex (n + 1) ul)
    have hKcomp : IsComplete (voronoiList V (truncateSimplex (n + 1) ul)) :=
      (p2g_CLOSED_VORONOI_LIST V (truncateSimplex (n + 1) ul)).isComplete
    obtain ⟨y, hyK, hynorm⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomp hKconv
      (omegaListN V ul n)
    -- bound-variable 形状调 ciInf_le（Mathlib Projection 文件 δ_le 同法；对
    -- 构造项 `⟨z, hz⟩` 直接展开会触发 isDefEq 死循环）
    have hstep : ∀ w : ↥(voronoiList V (truncateSimplex (n + 1) ul)),
        ‖omegaListN V ul n - y‖ ≤ ‖omegaListN V ul n - ↑w‖ := by
      intro w
      rw [hynorm]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun v => norm_nonneg _⟩ w
    have hmin : ∀ z ∈ voronoiList V (truncateSimplex (n + 1) ul),
        dist (omegaListN V ul n) y ≤ dist (omegaListN V ul n) z := by
      intro z hz
      rw [dist_eq_norm, dist_eq_norm]
      exact hstep ⟨z, hz⟩
    exact (Classical.epsilon_spec
      (p := fun y : V3 => y ∈ voronoiList V (truncateSimplex (n + 1) ul) ∧
        ∀ z ∈ voronoiList V (truncateSimplex (n + 1) ul),
          dist (omegaListN V ul n) y ≤ dist (omegaListN V ul n) z)
      ⟨y, hyK, hmin⟩).1

/-! ### §4 Voronoi list 的面链（PA6 正本落地，本为链复制） -/

/-- 桥（PA6 正本 `p6_voronoi_list_eq_inters_bis`，PackingAuto7 桥的自足核心拷贝）：
Voronoi list 是头的闭胞被其余表点平分面切割。PA6 正本落地，本为链复制。 -/
private theorem p2g_voronoi_list_eq_inters_bis (V : Set V3) (ul : List V3)
    (hsub : setOfList ul ⊆ V) (h1 : 1 ≤ ul.length) :
    voronoiList V ul =
      voronoiClosed V (hdV ul) ∩ ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul} := by
  have hhd_mem : hdV ul ∈ setOfList ul := by
    cases ul with
    | nil => exact absurd h1 (by simp)
    | cons a t => simp [setOfList, hdV]
  ext x
  constructor
  · intro hx
    have hx2 : x ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul} := hx
    rw [Set.mem_sInter] at hx2
    have hx' : ∀ w ∈ setOfList ul, ∀ w' ∈ V, dist x w ≤ dist x w' := by
      intro w hw w' hw'
      have hzw : x ∈ voronoiClosed V w := hx2 _ (by simpa using ⟨w, hw, rfl⟩)
      exact hzw w' hw'
    have hA : ∀ w ∈ V, dist x (hdV ul) ≤ dist x w := hx' (hdV ul) hhd_mem
    have hB : ∀ w ∈ setOfList ul, dist x (hdV ul) = dist x w := by
      intro w hw
      exact le_antisymm (hA w (hsub hw)) (hx' w hw (hdV ul) (hsub hhd_mem))
    refine ⟨hA, ?_⟩
    rw [Set.mem_sInter]
    intro T hT
    obtain ⟨u, hu, rfl⟩ := by simpa using hT
    exact hB u hu
  · intro hx
    have hx1 : ∀ w' ∈ V, dist x (hdV ul) ≤ dist x w' := hx.1
    have hxI : ∀ T ∈ {bis (hdV ul) u | u ∈ setOfList ul}, x ∈ T := hx.2
    show x ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul}
    rw [Set.mem_sInter]
    intro U hU
    obtain ⟨u, hu, rfl⟩ := by simpa using hU
    intro w hw
    have hC : dist x (hdV ul) = dist x u := hxI _ (by simpa using ⟨u, hu, rfl⟩)
    rw [← hC]
    exact hx1 w hw

/-- Rogers.hl:52 `KHEJKCI_GEN`（PA6 正本）。PA6 正本落地，本为链复制。 -/
private theorem p2g_KHEJKCI_GEN (V : Set V3) (k r : ℕ) (ul vl : List V3)
    (hs : saturated V) (hP : Packing V) (hk : barV V k ul) (hr : barV V r vl)
    (hinit : initialSublist ul vl) :
    FaceOf (voronoiList V vl) (voronoiList V ul) := by
  obtain ⟨h, t, hcons, -⟩ := p2g_BARV_CONS V k ul hk
  obtain ⟨yl, hvle⟩ := hinit
  have hvcons : vl = h :: (t ++ yl) := by rw [hvle, hcons]; rfl
  have hsubU : setOfList (h :: t) ⊆ V := by rw [← hcons]; exact p2g_BARV_SUBSET V k ul hk
  have hsubV : setOfList (h :: (t ++ yl)) ⊆ V := by
    rw [← hvcons]; exact p2g_BARV_SUBSET V r vl hr
  rw [hcons, hvcons,
    p2g_voronoi_list_eq_inters_bis V (h :: t) hsubU (by simp),
    p2g_voronoi_list_eq_inters_bis V (h :: (t ++ yl)) hsubV (by simp)]
  have hsubTT : setOfList (h :: t) ⊆ setOfList (h :: (t ++ yl)) := by
    intro u hu
    simp only [setOfList, List.mem_cons] at hu ⊢
    rcases hu with rfl | hut
    · exact Or.inl rfl
    · exact Or.inr (List.mem_append_left _ hut)
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    rw [Set.mem_sInter]
    rintro T ⟨u, hu, rfl⟩
    exact hx2 _ (by simpa using ⟨u, hsubTT hu, rfl⟩)
  · exact Convex.inter (p2g_CONVEX_VORONOI_CLOSED V (hdV (h :: (t ++ yl))))
      (convex_sInter fun T hT => by
        obtain ⟨u, -, rfl⟩ := by simpa using hT
        exact p2g_CONVEX_BIS _ _)
  · intro a b x ha hb hx hseg
    obtain ⟨ha1, -⟩ := ha
    obtain ⟨hb1, -⟩ := hb
    obtain ⟨hx1, hx2⟩ := hx
    have hstep : ∀ u ∈ setOfList (h :: (t ++ yl)), a ∈ bis h u ∧ b ∈ bis h u := by
      intro u hu
      have huV : u ∈ V := hsubV hu
      have hxT : x ∈ bis h u := hx2 _ (by simpa using ⟨u, hu, rfl⟩)
      exact (p2g_BIS_FACE_OF_BIS_LE h u).2.2 a b x (ha1 u huV) (hb1 u huV) hxT hseg
    refine ⟨⟨ha1, ?_⟩, ⟨hb1, ?_⟩⟩
    · rw [Set.mem_sInter]
      rintro T ⟨u, hu, rfl⟩
      exact (hstep u hu).1
    · rw [Set.mem_sInter]
      rintro T ⟨u, hu, rfl⟩
      exact (hstep u hu).2

/-- pack3.hl:2260 `VORONOI_LIST_CANONICAL`。-- NEEDS: PA5:1492 正本落地后替换
（PA2 侧不可 import，链复制桩）。 -/
private theorem p2g_VORONOI_LIST_CANONICAL (V : Set V3) (ul : List V3) (h : V3) (t : List V3)
    (hV : Packing V) (hs : saturated V) (hsub : setOfList ul ⊆ V) (hcons : ul = h :: t) :
    ∃ K : Set (Set V3), K.Finite ∧
      voronoiList V ul = ((affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K) ∧
      (∀ a ∈ K, ∃ v ∈ V, v ≠ h ∧ (a = bisLe v h ∨ a = bisLe h v)) ∧
      (∀ K' ⊂ K, voronoiList V ul ⊂ ((affineSpan ℝ (voronoiList V ul : Set V3) : Set V3) ∩ ⋂₀ K')) :=
  sorry

/-- Rogers.hl:172 `VORONOI_BARV_CANONICAL`（PA6 正本）。PA6 正本落地，本为链复制。 -/
private theorem p2g_VORONOI_BARV_CANONICAL (V : Set V3) (k : ℕ) (ul : List V3)
    (hP : Packing V) (hs : saturated V) (hk : barV V k ul) :
    ∃ K : Set (Set V3), K.Finite ∧
      voronoiList V ul = (affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K ∧
      (∀ a ∈ K, ∃ v ∈ V, v ≠ hdV ul ∧ (a = bisLe v (hdV ul) ∨ a = bisLe (hdV ul) v)) ∧
      ∀ K' ⊂ K, voronoiList V ul ⊂
        (affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K' := by
  obtain ⟨h, t, hcons, -⟩ := p2g_BARV_CONS V k ul hk
  have hhdev : hdV (h :: t) = h := rfl
  rw [hcons, hhdev]
  exact p2g_VORONOI_LIST_CANONICAL V (h :: t) h t hP hs
    (by rw [← hcons]; exact p2g_BARV_SUBSET V k ul hk) rfl

/-- 前缀判定（PA6 私件 `p6_initial_sublist_prefix`）。PA6 正本落地，本为链复制。 -/
private theorem p2g_initial_sublist_prefix {w u z : List V3}
    (h1 : initialSublist w z) (h2 : initialSublist u z) (hlen : w.length ≤ u.length) :
    initialSublist w u := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  have heq : w ++ t1 = u ++ t2 := by rw [← ht1, ← ht2]
  rcases List.append_eq_append_iff.mp heq with hcase | hcase
  · obtain ⟨t, hw, -⟩ := hcase
    exact ⟨t, hw⟩
  · obtain ⟨t, hu, -⟩ := hcase
    rw [hu, List.length_append] at hlen
    have ht0 : t = [] := List.length_eq_zero_iff.mp (by omega)
    rw [ht0, List.append_nil] at hu
    exact ⟨[], by rw [hu, List.append_nil]⟩

/-- Rogers.hl:212 `HALFSPACE_EQ`。-- NEEDS: PA6:247 正本落地后替换（PA2 侧不可
import，链复制桩；PA6 本体亦为 sorry）。 -/
private theorem p2g_HALFSPACE_EQ (a : V3) (b : ℝ) (c : V3) (d : ℝ) :
    {x : V3 | a ⬝ᵥ x ≤ b} = {x : V3 | c ⬝ᵥ x ≤ d} ↔
      (∃ t : ℝ, c = t • a ∧ d = t * b ∧ 0 < t) ∨
        (a = 0 ∧ c = 0 ∧ ((0 ≤ b ∧ 0 ≤ d) ∨ (b < 0 ∧ d < 0))) :=
  sorry

/-- Rogers.hl:397 `HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS`（PA6 正本）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a v w : V3) (b : ℝ) (ha : a ≠ 0)
    (h : {x : V3 | a ⬝ᵥ x ≤ b} = bisLe v w) :
    {x : V3 | a ⬝ᵥ x = b} = bis v w := by
  have e0 : ∀ y : V3, ((2 : ℝ) • (w - v)) ⬝ᵥ y = 2 * ((w - v) ⬝ᵥ y) :=
    fun y => smul_dotProduct 2 ((w - v : V3) : Fin 3 → ℝ) (y : Fin 3 → ℝ)
  have h2 : {x : V3 | a ⬝ᵥ x ≤ b} =
    {y : V3 | ((2 : ℝ) • (w - v)) ⬝ᵥ y ≤ w ⬝ᵥ w - v ⬝ᵥ v} := by
    rw [h, p2g_BIS_LE_EQ_HALFSPACE]
    ext y
    simp only [Set.mem_setOf_eq, e0]
  rcases (p2g_HALFSPACE_EQ a b ((2 : ℝ) • (w - v)) (w ⬝ᵥ w - v ⬝ᵥ v)).1 h2 with
    hcase | hcase
  · obtain ⟨t, ht1, ht2, ht3⟩ := hcase
    have e1 : ∀ y : V3, 2 * ((w - v) ⬝ᵥ y) = t * (a ⬝ᵥ y) := by
      intro y
      have e11 : ((2 : ℝ) • (w - v)) ⬝ᵥ y =
          t * ((a : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ)) := by
        rw [ht1]
        exact smul_dotProduct t _ _
      rw [← e11, e0]
    have e2 : t * b = w ⬝ᵥ w - v ⬝ᵥ v := ht2.symm
    rw [p2g_BIS_EQ_HYPERPLANE v w]
    ext y
    simp only [Set.mem_setOf_eq, e1, ← e2]
    constructor
    · intro hh
      rw [hh]
    · intro hh
      exact mul_left_cancel₀ (ne_of_gt ht3) hh
  · exact absurd hcase.1 ha

/-- Rogers.hl:417 `FACET_OF_POLYHEDRON_EXPLICIT_BIS`（PA6 正本）。PA6 正本落地，
本为链复制。 -/
private theorem p2g_FACET_OF_POLYHEDRON_EXPLICIT_BIS (V : Set V3) (K : Set (Set V3)) (s : Set V3)
    (u : V3) (h1 : K.Finite) (h2 : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ K)
    (h3 : ∀ a ∈ K, ∃ v ∈ V, v ≠ u ∧ (a = bisLe v u ∨ a = bisLe u v))
    (h4 : ∀ K' ⊂ K, s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ K') :
    ∀ c : Set V3, FacetOf c s ↔
      ∃ v ∈ V, (bisLe v u ∈ K ∨ bisLe u v ∈ K) ∧ c = s ∩ bis u v := by
  classical
  intro c
  -- every bisector constraint is a nonzero linear halfspace (Rogers.hl:417)
  obtain ⟨a, b, hab⟩ : ∃ a : Set V3 → V3, ∃ b : Set V3 → ℝ,
      ∀ h ∈ K, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h} := by
    have hsk : ∀ h : Set V3, ∃ a : V3, ∃ b : ℝ,
        h ∈ K → (a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}) := by
      intro h
      by_cases hK : h ∈ K
      · obtain ⟨v, hvV, hvu, hcase⟩ := h3 h hK
        rcases hcase with heq | heq
        · refine ⟨(2 : ℝ) • (u - v), u ⬝ᵥ u - v ⬝ᵥ v, ?_⟩
          intro _
          refine ⟨?_, ?_⟩
          · intro hcon
            exact hvu (sub_eq_zero.mp
              ((smul_eq_zero.mp hcon).resolve_left (by norm_num))).symm
          · rw [heq, p2g_BIS_LE_EQ_HALFSPACE]
            ext x
            simp only [Set.mem_setOf_eq, WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
        · refine ⟨(2 : ℝ) • (v - u), v ⬝ᵥ v - u ⬝ᵥ u, ?_⟩
          intro _
          refine ⟨?_, ?_⟩
          · intro hcon
            exact hvu (sub_eq_zero.mp
              ((smul_eq_zero.mp hcon).resolve_left (by norm_num)))
          · rw [heq, p2g_BIS_LE_EQ_HALFSPACE]
            ext x
            simp only [Set.mem_setOf_eq, WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
      · exact ⟨0, 0, fun hm => absurd hm hK⟩
    choose a b hab using hsk
    exact ⟨a, b, fun h hK => hab h hK⟩
  have hmain := FACET_OF_POLYHEDRON_EXPLICIT (s := s) (F := K) a b h1 h2 hab h4 c
  rw [hmain]
  constructor
  · rintro ⟨h, hK, rfl⟩
    obtain ⟨v, hvV, hvu, hcase⟩ := h3 h hK
    rcases hcase with heq | heq
    · have hplane := p2g_HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a h) v u (b h)
        (hab h hK).1 ((hab h hK).2.symm.trans heq)
      exact ⟨v, hvV, Or.inl (by rw [← heq]; exact hK), by rw [hplane, p2g_BIS_SYM]⟩
    · have hplane := p2g_HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a h) u v (b h)
        (hab h hK).1 ((hab h hK).2.symm.trans heq)
      exact ⟨v, hvV, Or.inr (by rw [← heq]; exact hK), by rw [hplane]⟩
  · rintro ⟨v, hvV, hKmem, rfl⟩
    rcases hKmem with hKmem | hKmem
    · have hplane := p2g_HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a (bisLe v u))
        v u (b (bisLe v u)) (hab _ hKmem).1 (hab _ hKmem).2.symm
      exact ⟨bisLe v u, hKmem, by rw [hplane, p2g_BIS_SYM]⟩
    · have hplane := p2g_HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a (bisLe u v))
        u v (b (bisLe u v)) (hab _ hKmem).1 (hab _ hKmem).2.symm
      exact ⟨bisLe u v, hKmem, by rw [hplane]⟩

/-- Rogers.hl:523 `IDBEZAL`（PA6 正本）。PA6 正本落地，本为链复制。 -/
private theorem p2g_IDBEZAL (V : Set V3) (ul : List V3) (k : ℕ) (F : Set V3)
    (hs : saturated V) (hP : Packing V) (hbar : barV V k ul) (h3 : k < 3) :
    FacetOf F (voronoiList V ul) ↔
      ∃ vl : List V3, F = voronoiList V vl ∧ barV V (k + 1) vl ∧
        truncateSimplex k vl = ul := by
  constructor
  · intro hF
    obtain ⟨h, t, hcons, hhd⟩ := p2g_BARV_CONS V k ul hbar
    have hcons' : ul = hdV ul :: t := hcons.trans (by rw [← hhd])
    have hsub : setOfList ul ⊆ V := p2g_BARV_SUBSET V k ul hbar
    obtain ⟨K, hKfin, hKeq, hKprop, hKmin⟩ := p2g_VORONOI_BARV_CANONICAL V k ul hP hs hbar
    obtain ⟨v, hvV, hKin, hFv⟩ :=
      (p2g_FACET_OF_POLYHEDRON_EXPLICIT_BIS V K (voronoiList V ul) (hdV ul) hKfin hKeq
        hKprop hKmin F).mp hF
    have hts : truncateSimplex k (ul ++ [v]) = ul :=
      ((p2g_TRUNCATE_SIMPLEX_INITIAL_SUBLIST k ul (ul ++ [v])).2
        ⟨p2g_INITIAL_SUBLIST_APPEND ul [v], hbar.1⟩).1
    have hFext : voronoiList V (ul ++ [v]) = F := by
      rw [← p2g_VORONOI_LIST_INTER_BIS V ul v (hdV ul) t hsub hvV hcons', hFv]
    have hbarext : barV V (k + 1) (ul ++ [v]) := by
      refine ⟨by rw [List.length_append, List.length_singleton, hbar.1], ?_⟩
      rintro w ⟨hwinit, hwpos⟩
      by_cases hlen : w.length ≤ k + 1
      · have hwinit' : initialSublist w ul :=
          p2g_initial_sublist_prefix hwinit (p2g_INITIAL_SUBLIST_APPEND ul [v])
            (by rw [hbar.1]; exact hlen)
        exact hbar.2 w ⟨hwinit', hwpos⟩
      · have hlenEq : w.length = (ul ++ [v]).length := by
          have hwle := p2g_INITIAL_SUBLIST_LENGTH_LE hwinit
          rw [List.length_append, List.length_singleton, hbar.1] at hwle ⊢
          omega
        have hwEq : w = ul ++ [v] :=
          p2g_INITIAL_SUBLIST_UNIQUE hwinit (p2g_INITIAL_SUBLIST_REFL (ul ++ [v])) hlenEq rfl
        subst hwEq
        have hlen4 : (ul ++ [v]).length = k + 2 := by
          rw [List.length_append, List.length_singleton, hbar.1]
        refine ⟨by rw [hlen4]; omega, ?_, ?_⟩
        · intro z hz
          rcases List.mem_append.1 hz with hz | hz
          · exact hsub hz
          · rw [List.mem_singleton] at hz
            rw [hz]
            exact hvV
        · rw [hFext, hlen4]
          have h1 := hF.2.2
          rw [p2g_AFF_DIM_VORONOI_LIST V ul k hbar] at h1
          omega
    exact ⟨ul ++ [v], hFext.symm, hbarext, hts⟩
  · rintro ⟨vl, hFvl, hbarvl, hts⟩
    obtain ⟨hinit, hlenul⟩ := (p2g_TRUNCATE_SIMPLEX_INITIAL_SUBLIST k ul vl).1 ⟨hts, by
      have := hbarvl.1
      omega⟩
    rw [hFvl]
    refine ⟨p2g_KHEJKCI_GEN V k (k + 1) ul vl hs hP hbar hbarvl hinit, ?_, ?_⟩
    · exact p2g_BARV_IMP_VORONOI_LIST_NOT_EMPTY V vl (k + 1) hbarvl
    · rw [p2g_AFF_DIM_VORONOI_LIST V vl (k + 1) hbarvl, p2g_AFF_DIM_VORONOI_LIST V ul k hbar]
      omega

/-- pack3.hl:2297 `POLYHEDRON_VORONOI_LIST`。-- NEEDS: PA5:1500 正本落地后替换
（PA2 侧不可 import，链复制桩）。 -/
private theorem p2g_POLYHEDRON_VORONOI_LIST (V : Set V3) (ul : List V3) (hV : Packing V)
    (hs : saturated V) (hsub : setOfList ul ⊆ V) : polyhedron (voronoiList V ul) :=
  sorry

/-- pack3.hl:2355 `POLYTOPE_VORONOI_LIST`。-- NEEDS: PA5:1501 正本落地后替换
（PA2 侧不可 import，链复制桩）。 -/
private theorem p2g_POLYTOPE_VORONOI_LIST (V : Set V3) (ul : List V3) (hV : Packing V)
    (hs : saturated V) (hsub : setOfList ul ⊆ V) (hne : ul ≠ []) :
    polytope (voronoiList V ul) :=
  sorry

/-- pack3.hl:2355 `POLYTOPE_VORONOI_LIST_BARV`（PA5 正本）。PA5 正本落地，本为链复制。 -/
private theorem p2g_POLYTOPE_VORONOI_LIST_BARV (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hs : saturated V) (hbar : barV V k ul) :
    polytope (voronoiList V ul) := by
  have hbl := hbar.1
  exact p2g_POLYTOPE_VORONOI_LIST V ul hV hs (p2g_BARV_SUBSET V k ul hbar) (by
    intro h0
    simp [h0] at hbl)

/-- 桥助（PA6 私件 `p6_sSup_mem_closed`）：非空有上界闭集的上确界属于该集。
PA6 正本落地，本为链复制。 -/
private theorem p2g_sSup_mem_closed (I : Set ℝ) (hne : I.Nonempty) (hbdd : BddAbove I)
    (hcl : IsClosed I) : sSup I ∈ I := by
  by_contra hnot
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl (sSup I) (by
    simpa using hnot)
  have hbound : ∀ x ∈ I, x ≤ sSup I - ε := by
    intro x hx
    have hxle : x ≤ sSup I := le_csSup hbdd hx
    have hlt : x < sSup I := by
      rcases eq_or_lt_of_le hxle with he | hl
      · exact absurd (he ▸ hx) hnot
      · exact hl
    have hballmem : x ∉ Metric.ball (sSup I) ε := fun hm => hball hm hx
    have hdist : ε ≤ dist x (sSup I) :=
      le_of_not_gt fun hlt' => hballmem (Metric.mem_ball.2 hlt')
    rw [Real.dist_eq, abs_of_neg (by linarith)] at hdist
    linarith
  have hsup := csSup_le hne hbound
  linarith

/-- 桥助（PA6 私件 `p6_two_distinct_of_affDim_pos`）：正维紧凸集有两相异点。
PA6 正本落地，本为链复制。 -/
private theorem p2g_two_distinct_of_affDim_pos {s : Set V3} (hsne : s.Nonempty)
    (hdim : 0 < affDim s) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  by_contra hall
  push_neg at hall
  obtain ⟨x₀, hx₀⟩ := hsne
  have hseq : s = {x₀} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨hx₀, fun z hz => hall z hz x₀ hx₀⟩
  rw [hseq, affDim_singleton] at hdim
  omega

/-- 边界点引理（PA6 私件 `p6_mem_hull_insert_facet`，HOL Rogers.hl:694 背后）：
紧多面体的点在 `p0` 与某个面的壳的并里（或是 `p0` 本身）。PA6 正本落地，
本为链复制。 -/
private theorem p2g_mem_hull_insert_facet (s : Set V3) (p0 v : V3)
    (hsp : polyhedron s) (hcomp : _root_.IsCompact s) (hp0 : p0 ∈ s) (hv : v ∈ s) :
    v = p0 ∨ ∃ f : Set V3, FacetOf f s ∧ v ∈ convexHull ℝ (insert p0 f) := by
  classical
  by_cases hv0 : v = p0
  · exact Or.inl hv0
  · right
    have hdnz : v - p0 ≠ 0 := sub_ne_zero.2 hv0
    have hnormpos : (0 : ℝ) < ‖v - p0‖ := norm_pos_iff.2 hdnz
    have hcont : Continuous fun t : ℝ => p0 + t • (v - p0) := by fun_prop
    have hIcl : IsClosed {t : ℝ | p0 + t • (v - p0) ∈ s} :=
      (IsCompact.isClosed hcomp).preimage hcont
    have hone : (1 : ℝ) ∈ {t : ℝ | p0 + t • (v - p0) ∈ s} := by
      simp only [Set.mem_setOf_eq, one_smul, add_sub_cancel]
      exact hv
    have hzero : (0 : ℝ) ∈ {t : ℝ | p0 + t • (v - p0) ∈ s} := by
      simp only [Set.mem_setOf_eq, zero_smul, add_zero]
      exact hp0
    have hbdd : BddAbove {t : ℝ | p0 + t • (v - p0) ∈ s} := by
      obtain ⟨C, hC⟩ := IsCompact.exists_isMaxOn hcomp ⟨p0, hp0⟩
        (f := fun x : V3 => ‖x‖) (by fun_prop)
      refine ⟨(2 * ‖C‖) / ‖v - p0‖, ?_⟩
      intro t ht
      have hC0 : ‖p0‖ ≤ ‖C‖ := hC.2 hp0
      have h1 : ‖t • (v - p0)‖ ≤ ‖C‖ + ‖p0‖ := by
        have h2 : ‖t • (v - p0)‖ = ‖(p0 + t • (v - p0)) - p0‖ := by
          rw [add_sub_cancel_left]
        rw [h2]
        calc ‖(p0 + t • (v - p0)) - p0‖ ≤ ‖p0 + t • (v - p0)‖ + ‖p0‖ := norm_sub_le _ _
          _ ≤ ‖C‖ + ‖p0‖ := by
              exact add_le_add (hC.2 ht) (le_refl _)
      have h3 : |t| * ‖v - p0‖ ≤ ‖C‖ + ‖p0‖ := by
        rw [norm_smul, Real.norm_eq_abs] at h1
        exact h1
      have h4 : t * ‖v - p0‖ ≤ ‖C‖ + ‖p0‖ := by
        rcases abs_choice t with hc | hc
        · rw [← hc]
          exact h3
        · have ht0 : t ≤ 0 := by
            have habs : 0 ≤ |t| := abs_nonneg t
            linarith
          have hd0 : 0 ≤ ‖v - p0‖ := norm_nonneg _
          have hS0 : 0 ≤ ‖C‖ + ‖p0‖ := by
            have h1' : 0 ≤ ‖C‖ := norm_nonneg _
            have h2' : 0 ≤ ‖p0‖ := norm_nonneg _
            linarith
          nlinarith
      exact (le_div_iff₀ hnormpos).2 (by linarith)
    set T := sSup {t : ℝ | p0 + t • (v - p0) ∈ s} with hTdef
    have hTmem : p0 + T • (v - p0) ∈ s :=
      hTdef ▸ p2g_sSup_mem_closed _ ⟨0, hzero⟩ hbdd hIcl
    have hT1 : (1 : ℝ) ≤ T := le_csSup hbdd hone
    -- the farthest point of the polytope on the ray is not in the relative interior
    have haff : ∀ r : ℝ, p0 + r • (v - p0) ∈ (affineSpan ℝ s : Set V3) := by
      intro r
      have hA0 : p0 ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hp0
      have hdir : (v - p0 : V3) ∈ (affineSpan ℝ s).direction := by
        rw [direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hv hp0
      have hv2 := AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ r hdir) hA0
      rw [vadd_eq_add, add_comm] at hv2
      exact hv2
    have hwint : p0 + T • (v - p0) ∉ intrinsicInterior ℝ s := by
      intro hm
      obtain ⟨-, ε, hε, hball⟩ := mem_rint_iff.1 hm
      have hpos : 0 < ε / (2 * ‖v - p0‖) := by
        apply div_pos hε
        linarith
      have hd : dist (p0 + (T + ε / (2 * ‖v - p0‖)) • (v - p0))
          (p0 + T • (v - p0)) < ε := by
        rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, add_sub_cancel_left,
          norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        field_simp
        linarith
      have hmem : (T + ε / (2 * ‖v - p0‖)) ∈
          {t : ℝ | p0 + t • (v - p0) ∈ s} :=
        Set.mem_setOf.2 (hball ⟨hd, haff _⟩)
      have hle := le_csSup hbdd hmem
      linarith
    rw [RELATIVE_INTERIOR_OF_POLYHEDRON hsp] at hwint
    have hU : p0 + T • (v - p0) ∈ ⋃₀ {f : Set V3 | FacetOf f s} := by
      by_contra hcon
      exact hwint ((Set.mem_sdiff _).2 ⟨hTmem, hcon⟩)
    obtain ⟨f, hf, hwf⟩ := Set.mem_sUnion.1 hU
    refine ⟨f, hf, ?_⟩
    have hTpos : (0 : ℝ) < T := by linarith
    have hseg : v ∈ convexHull ℝ {p0, p0 + T • (v - p0)} := by
      rw [convexHull_pair, segment_eq_image' ℝ p0 (p0 + T • (v - p0))]
      have hθ1 : (0:ℝ) ≤ 1 / T := div_nonneg (by norm_num) hTpos.le
      have hθ2 : 1 / T ≤ 1 := (div_le_one hTpos).2 hT1
      refine ⟨1 / T, ⟨hθ1, hθ2⟩, ?_⟩
      show p0 + (1 / T) • ((p0 + T • (v - p0)) - p0) = v
      rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hTpos),
        one_smul, add_sub_cancel]
    refine convexHull_mono ?_ hseg
    intro z hz
    rcases Set.mem_insert_iff.1 hz with hz | hz
    · subst hz
      exact Set.mem_insert z f
    · subst hz
      exact Set.mem_insert_of_mem _ hwf

/-- 紧多面体 = `p` 与各面壳的并（PA6 私件 `p6_union_convex_hull_facets`）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_union_convex_hull_facets (s : Set V3) (p : V3) (hsp : polyhedron s)
    (hcomp : _root_.IsCompact s) (hdim : 0 < affDim s) (hp : p ∈ s) :
    s = ⋃₀ {convexHull ℝ (insert p f) | f ∈ {f : Set V3 | FacetOf f s}} := by
  classical
  have hsne : s.Nonempty := ⟨p, hp⟩
  have hconv : Convex ℝ s := POLYHEDRON_IMP_CONVEX hsp
  obtain ⟨x, hx, y, hy, hxy⟩ := p2g_two_distinct_of_affDim_pos hsne hdim
  have hfacet : ∃ f : Set V3, FacetOf f s := by
    rcases eq_or_ne x p with hx0 | hx0
    · obtain ⟨f, hf, -⟩ := (p2g_mem_hull_insert_facet s p y hsp hcomp hp hy).resolve_left
        (fun heq => hxy (by rw [hx0]; exact heq.symm))
      exact ⟨f, hf⟩
    · obtain ⟨f, hf, -⟩ := (p2g_mem_hull_insert_facet s p x hsp hcomp hp hx).resolve_left hx0
      exact ⟨f, hf⟩
  ext v
  constructor
  · intro hv
    by_cases hv0 : v = p
    · obtain ⟨f, hf⟩ := hfacet
      rw [hv0]
      exact Set.mem_sUnion.2 ⟨convexHull ℝ (insert p f), ⟨f, hf, rfl⟩,
        subset_convexHull ℝ _ (Set.mem_insert p f)⟩
    · obtain ⟨f, hf, hvm⟩ :=
        (p2g_mem_hull_insert_facet s p v hsp hcomp hp hv).resolve_left hv0
      exact Set.mem_sUnion.2 ⟨convexHull ℝ (insert p f), ⟨f, hf, rfl⟩, hvm⟩
  · rintro ⟨T, ⟨f, hf, rfl⟩, hvT⟩
    have hsub : insert p f ⊆ s := by
      intro z hz
      rcases Set.mem_insert_iff.1 hz with hz | hz
      · rw [hz]; exact hp
      · exact hf.1.1 hz
    exact convexHull_min hsub hconv hvT

/-- Rogers.hl:694 `VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS`（PA6 正本）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS (V : Set V3) (ul : List V3)
    (k : ℕ) (p : V3) (hP : Packing V) (hs : saturated V) (hbar : barV V k ul) (hk3 : k < 3)
    (hp : p ∈ voronoiList V ul) :
    voronoiList V ul =
      ⋃₀ {convexHull ℝ (insert p (voronoiList V vl)) | vl ∈ {vl : List V3 |
        barV V (k + 1) vl ∧ truncateSimplex k vl = ul}} := by
  classical
  have hcomp : _root_.IsCompact (voronoiList V ul) :=
    POLYTOPE_IMP_COMPACT (p2g_POLYTOPE_VORONOI_LIST_BARV V ul k hP hs hbar)
  have hsp : polyhedron (voronoiList V ul) :=
    p2g_POLYHEDRON_VORONOI_LIST V ul hP hs (p2g_BARV_SUBSET V k ul hbar)
  have hdim : 0 < affDim (voronoiList V ul) := by
    rw [p2g_AFF_DIM_VORONOI_LIST V ul k hbar]
    omega
  have hmain := p2g_union_convex_hull_facets (voronoiList V ul) p hsp hcomp hdim hp
  have hfam : {convexHull ℝ (insert p f) | f ∈ {f : Set V3 |
      FacetOf f (voronoiList V ul)}} =
      {convexHull ℝ (insert p (voronoiList V vl)) | vl ∈ {vl : List V3 |
        barV V (k + 1) vl ∧ truncateSimplex k vl = ul}} := by
    ext T
    constructor
    · rintro ⟨f, hf, hTeq⟩
      obtain ⟨vl, hvl1, hvl2, hvl3⟩ := (p2g_IDBEZAL V ul k f hs hP hbar hk3).mp hf
      exact ⟨vl, ⟨hvl2, hvl3⟩, by rw [← hTeq, hvl1]⟩
    · rintro ⟨vl, hmem, hTeq⟩
      obtain ⟨hvl2, hvl3⟩ := hmem
      have hf : FacetOf (voronoiList V vl) (voronoiList V ul) :=
        (p2g_IDBEZAL V ul k (voronoiList V vl) hs hP hbar hk3).mpr ⟨vl, rfl, hvl2, hvl3⟩
      exact ⟨voronoiList V vl, hf, by rw [hTeq]⟩
  rw [hmain, hfam]

/-! ### §5 sUnion bookkeeping + GLTVHUM_lemma1（PA6 正本落地，本为链复制） -/

/-- `hull (A ∪ hull B) = hull (A ∪ B)`（PA6 私件 `p6_convexHull_union_hull`）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_convexHull_union_hull (A B : Set V3) :
    convexHull ℝ (A ∪ convexHull ℝ B) = convexHull ℝ (A ∪ B) := by
  refine subset_antisymm ?_ ?_
  · refine convexHull_min ?_ (convex_convexHull ℝ (A ∪ B))
    intro z hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · exact subset_convexHull ℝ (A ∪ B) (Set.mem_union_left _ hz)
    · exact (convexHull_mono (Set.subset_union_right : B ⊆ A ∪ B)) hz
  · refine convexHull_min ?_ (convex_convexHull ℝ (A ∪ convexHull ℝ B))
    intro z hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · exact subset_convexHull ℝ (A ∪ convexHull ℝ B) (Set.mem_union_left _ hz)
    · exact subset_convexHull ℝ (A ∪ convexHull ℝ B)
        (Set.mem_union_right _ (subset_convexHull ℝ B hz))

/-- image-同构族并相等（PA6 私件 `p6_sUnion_image_congr`）。PA6 正本落地，
本为链复制。 -/
private theorem p2g_sUnion_image_congr {α : Type*} {F : Set α} {f g : α → Set V3}
    (h : ∀ x ∈ F, f x = g x) : ⋃₀ {f x | x ∈ F} = ⋃₀ {g x | x ∈ F} := by
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, hT, hz⟩
    obtain ⟨x, hx, rfl⟩ := hT
    exact ⟨g x, ⟨x, hx, rfl⟩, h x hx ▸ hz⟩
  · rintro ⟨T, hT, hz⟩
    obtain ⟨x, hx, rfl⟩ := hT
    exact ⟨f x, ⟨x, hx, rfl⟩, (h x hx).symm ▸ hz⟩

/-- 星引理（PA6 私件 `p6_convexHull_sUnion_left`；HOL convex1.ml:2999）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_convexHull_sUnion_left (S : Set V3) (𝒞 : Set (Set V3))
    (hne : 𝒞.Nonempty) (hconv : Convex ℝ (⋃₀ 𝒞)) :
    convexHull ℝ (S ∪ ⋃₀ 𝒞) = ⋃₀ {convexHull ℝ (S ∪ c) | c ∈ 𝒞} := by
  classical
  obtain ⟨c₀, hc₀⟩ := hne
  refine subset_antisymm ?_ ?_
  · -- the hull is inside the union of the pairwise hulls
    intro x hx
    by_cases hSe : S.Nonempty
    · by_cases hUe : (⋃₀ 𝒞).Nonempty
      · have hxj : x ∈ convexJoin ℝ (convexHull ℝ S) (convexHull ℝ (⋃₀ 𝒞)) := by
          rw [← convexHull_union hSe hUe]
          exact hx
        obtain ⟨p, hp, q, hq, hseg⟩ := mem_convexJoin.1 hxj
        have hqU : q ∈ ⋃₀ 𝒞 := hconv.convexHull_eq ▸ hq
        obtain ⟨c₁, hc₁, hqc₁⟩ := Set.mem_sUnion.1 hqU
        refine ⟨convexHull ℝ (S ∪ c₁), ⟨c₁, hc₁, rfl⟩, ?_⟩
        obtain ⟨θ, ϑ, hθ0, hϑ0, hsum, hxq⟩ := hseg
        refine (convex_iff_segment_subset.1 (convex_convexHull ℝ (S ∪ c₁))
          ((convexHull_mono (Set.subset_union_left : S ⊆ S ∪ c₁)) hp)
          (subset_convexHull ℝ _ (Set.mem_union_right _ hqc₁))) ?_
        rw [segment_eq_image]
        refine (Set.mem_image _ _ _).2 ⟨ϑ, ⟨hϑ0, by linarith⟩, ?_⟩
        show (1 - ϑ) • p + ϑ • q = x
        rw [show 1 - ϑ = θ from by linarith]
        exact hxq
      · have hU0 : ⋃₀ 𝒞 = ∅ := Set.not_nonempty_iff_eq_empty.1 hUe
        rw [hU0, Set.union_empty] at hx
        exact ⟨convexHull ℝ (S ∪ c₀), ⟨c₀, hc₀, rfl⟩,
          (convexHull_mono (Set.subset_union_left : S ⊆ S ∪ c₀)) hx⟩
    · have hSe0 : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hSe
      have hx2 : x ∈ convexHull ℝ (⋃₀ 𝒞) := by
        rw [hSe0, Set.empty_union] at hx
        exact hx
      have hx3 : x ∈ ⋃₀ 𝒞 := hconv.convexHull_eq ▸ hx2
      obtain ⟨c₁, hc₁, xc₁⟩ := Set.mem_sUnion.1 hx3
      exact ⟨convexHull ℝ (S ∪ c₁), ⟨c₁, hc₁, rfl⟩, by
        rw [hSe0, Set.empty_union]
        exact subset_convexHull ℝ c₁ xc₁⟩
  · -- each member hull (S ∪ c) is inside the hull
    rintro x ⟨T, hT, hx⟩
    obtain ⟨c, hc, rfl⟩ := hT
    exact (convexHull_mono (Set.union_subset_union (Subset.refl _)
      (Set.subset_sUnion_of_mem hc))) hx

/-- Step lemma (C) of `GLTVHUM_lemma1`（PA6 私件 `p6_gltvhum_union_g`）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_gltvhum_union_g (V : Set V3) (wl : List V3) (k : ℕ) (hP : Packing V)
    (hs : saturated V) (hk3 : k < 3) (hbar : barV V k wl) :
    ⋃₀ {convexHull ℝ (insert (omegaListN V vl k) (voronoiList V vl)) | vl ∈
      {vl : List V3 | barV V (k + 1) vl ∧ truncateSimplex k vl = wl}} =
    voronoiList V wl := by
  have hp : omegaListN V wl k ∈ voronoiList V wl := by
    have h1 := p2g_OMEGA_LIST_N_IN_VORONOI_LIST V wl k k hbar (le_refl k)
    rwa [p2g_TRUNCATE_SIMPLEX_REFL k wl hbar.1] at h1
  rw [p2g_VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS V wl k (omegaListN V wl k) hP hs hbar
    hk3 hp]
  ext T
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, hT, hx⟩
    obtain ⟨vl, hbarvl, hts, rfl⟩ := hT
    obtain ⟨hbarvl, hts⟩ := hbarvl
    have homega : omegaListN V vl k = omegaListN V wl k := by
      have hlen : vl.length = k + 2 := hbarvl.1
      have h5 := p2g_OMEGA_LIST_N_LEMMA V vl k 0 (by omega)
      rw [Nat.add_zero, hts] at h5
      exact h5
    rw [homega] at hx
    refine ⟨convexHull ℝ (insert (omegaListN V wl k) (voronoiList V vl)),
      Set.mem_setOf.2 ⟨vl, ⟨hbarvl, hts⟩, rfl⟩, hx⟩
  · rintro ⟨t, hT, hx⟩
    obtain ⟨vl, hbarvl, hts, rfl⟩ := hT
    obtain ⟨hbarvl, hts⟩ := hbarvl
    have homega : omegaListN V vl k = omegaListN V wl k := by
      have hlen : vl.length = k + 2 := hbarvl.1
      have h5 := p2g_OMEGA_LIST_N_LEMMA V vl k 0 (by omega)
      rw [Nat.add_zero, hts] at h5
      exact h5
    rw [← homega] at hx
    refine ⟨convexHull ℝ (insert (omegaListN V vl k) (voronoiList V vl)),
      Set.mem_setOf.2 ⟨vl, ⟨hbarvl, hts⟩, rfl⟩, hx⟩

/-- `j..k` omega-窗拆分（PA6 私件 `p6_image_Icc_succ`）。PA6 正本落地，本为链复制。 -/
private theorem p2g_image_Icc_succ (f : ℕ → V3) (j k : ℕ) (hjk : j ≤ k) :
    {f i | i ∈ Finset.Icc j (k - 1)} ∪ {f k} = {f i | i ∈ Finset.Icc j k} := by
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, Finset.mem_Icc]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨k, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rcases eq_or_ne i k with rfl | hik
    · exact Or.inr rfl
    · exact Or.inl ⟨i, by omega, rfl⟩

/-- 族经 image 的重指标（PA6 私件 `p6_sUnion_image_image`）。PA6 正本落地，
本为链复制。 -/
private theorem p2g_sUnion_image_image {α β : Type*} {F : Set α} (g : α → β)
    (h : β → Set V3) :
    ⋃₀ {h (g x) | x ∈ F} = ⋃₀ {h y | y ∈ {g x | x ∈ F}} := by
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨x, hxF, rfl⟩, hzT⟩
    exact ⟨h (g x), ⟨g x, ⟨x, hxF, rfl⟩, rfl⟩, hzT⟩
  · rintro ⟨T, ⟨y, ⟨x, hxF, rfl⟩, rfl⟩, hzT⟩
    exact ⟨h (g x), ⟨x, hxF, rfl⟩, hzT⟩

/-- 单点指标的族并坍缩（PA6 私件 `p6_sUnion_singleton_image`，base case 触达）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_sUnion_singleton_image {α : Type*} (q : α → Set V3) (a : α) :
    ⋃₀ {q v | v ∈ ({a} : Set α)} = q a := by
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨T, ⟨v, rfl, rfl⟩, hzT⟩
    exact hzT
  · intro hz
    exact ⟨q a, ⟨a, rfl, rfl⟩, hz⟩

/-- Step lemma (A) of `GLTVHUM_lemma1`（PA6 私件 `p6_union_split`，HOL
Rogers.hl:905-942）。PA6 正本落地，本为链复制。 -/
private theorem p2g_union_split (V : Set V3) (ul : List V3) (j k : ℕ) (hjk : j ≤ k)
    (Q : List V3 → Set V3) :
    ⋃₀ {Q vl | vl ∈ {vl : List V3 | barV V (k + 1) vl ∧ truncateSimplex j vl = ul}} =
    ⋃₀ {⋃₀ {Q vl | vl ∈ {vl : List V3 | barV V (k + 1) vl ∧ truncateSimplex k vl = wl}} |
      wl ∈ {wl : List V3 | barV V k wl ∧ truncateSimplex j wl = ul}} := by
  classical
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨vl, ⟨hb, ht⟩, rfl⟩, hzT⟩
    have hlen : vl.length = k + 2 := hb.1
    have hbart : barV V k (truncateSimplex k vl) :=
      p2g_TRUNCATE_SIMPLEX_BARV V k (k + 1) vl hb (by omega)
    have htwl : truncateSimplex j (truncateSimplex k vl) = ul := by
      rw [p2g_TRUNCATE_TRUNCATE_SIMPLEX vl j k hjk (by omega)]
      exact ht
    refine ⟨⋃₀ {Q v | v ∈ {v : List V3 | barV V (k + 1) v ∧
      truncateSimplex k v = truncateSimplex k vl}},
      ⟨truncateSimplex k vl, ⟨hbart, htwl⟩, rfl⟩, ?_⟩
    exact ⟨Q vl, ⟨vl, ⟨hb, rfl⟩, rfl⟩, hzT⟩
  · rintro ⟨W, ⟨wl, ⟨hbw, htw⟩, rfl⟩, hzW⟩
    obtain ⟨T, ⟨v, ⟨hb, hvw⟩, rfl⟩, hzT⟩ := hzW
    have hlen : v.length = k + 2 := hb.1
    have htv : truncateSimplex j (truncateSimplex k v) = ul := by
      rw [hvw]
      exact htw
    exact ⟨Q v, ⟨v, ⟨hb,
      (p2g_TRUNCATE_TRUNCATE_SIMPLEX v j k hjk (by omega)).symm.trans htv⟩, rfl⟩, hzT⟩

/-- Rogers.hl:754 `NUMSEG_SUBSET_INDUCT`（PA6 正本）。PA6 正本落地，本为链复制。 -/
private theorem p2g_NUMSEG_SUBSET_INDUCT (s : Set ℕ) (a b : ℕ) (ha : a ∈ s)
    (hstep : ∀ k, a ≤ k → k + 1 ≤ b → k ∈ s → k + 1 ∈ s) :
    Set.Icc a b ⊆ s := by
  intro m hm
  have key : ∀ n : ℕ, a ≤ n → n ≤ b → n ∈ s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h1 h2
      rcases Nat.eq_or_lt_of_le h1 with heq | hlt
      · subst heq
        exact ha
      · have h5 : n - 1 ∈ s := ih (n - 1) (by omega) (by omega) (by omega)
        have h6 : n - 1 + 1 = n := by omega
        rw [← h6]
        exact hstep (n - 1) (by omega) (by omega) h5
  exact key m hm.1 hm.2

/-- Rogers.hl:778 `BARV_EXISTS`。-- NEEDS: PA6:660 正本落地后替换（PA2 侧不可
import，链复制桩；PA6 本体亦为 sorry）。 -/
private theorem p2g_BARV_EXISTS (V : Set V3) (wl : List V3) (k : ℕ) (hP : Packing V)
    (hs : saturated V) (hk3 : k < 3) (hbar : barV V k wl) :
    ∃ vl : List V3, barV V (k + 1) vl ∧ truncateSimplex k vl = wl :=
  sorry

/-- Rogers.hl:826 `GLTVHUM_lemma1`（PA6:869 正本真证，逐字链复制+改名）。
PA6 正本落地，本为链复制。 -/
private theorem p2g_GLTVHUM_lemma1 (V : Set V3) (ul : List V3) (j : ℕ) (hP : Packing V)
    (hs : saturated V) (hj : j < 3) (hbar : barV V j ul) :
    {k : ℕ | k ∈ (Finset.Icc j 3 : Set ℕ) ∧ voronoiList V ul =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (k - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V k vl ∧ truncateSimplex j vl = ul}}} = (Finset.Icc j 3 : Set ℕ) := by
  -- k-归纳（NUMSEG_SUBSET_INDUCT）。≡-claim：`barV V j` 家族是单点 {ul}
  -- （TRUNCATE_SIMPLEX_INITIAL_SUBLIST + TRUNCATE_SIMPLEX_REFL）。
  have hclaim : ∀ vl : List V3, barV V j vl ∧ truncateSimplex j vl = ul ↔ vl = ul := by
    intro vl
    constructor
    · rintro ⟨hbarvl, hts⟩
      have h1 := (p2g_TRUNCATE_SIMPLEX_INITIAL_SUBLIST j vl vl).2
        ⟨p2g_INITIAL_SUBLIST_REFL vl, hbarvl.1⟩
      exact (hts.symm.trans h1.1).symm
    · rintro rfl
      exact ⟨hbar, p2g_TRUNCATE_SIMPLEX_REFL _ _ hbar.1⟩
  -- base k=j：家族={ul}；j=0 用 VORONOI_LIST_SING+CENTER_IN_VORONOI_CELL+
  -- CONVEX_VORONOI_CLOSED，j>0 用 Icc_eq_empty+CONVEX_VORONOI_LIST。
  have hbase : voronoiList V ul =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (j - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V j vl ∧ truncateSimplex j vl = ul}} := by
    have hsingleton : {vl : List V3 | barV V j vl ∧ truncateSimplex j vl = ul} = {ul} := by
      ext v
      simpa only [Set.mem_setOf_eq, Set.mem_singleton_iff] using hclaim v
    rw [hsingleton, p2g_sUnion_singleton_image]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 (show ul.length = 1 from hbar.1)
      rw [p2g_VORONOI_LIST_SING, show (0 : ℕ) - 1 = 0 from by omega]
      have h0 : {omegaListN V [y] i | i ∈ Finset.Icc 0 0} = {y} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Finset.mem_Icc]
        constructor
        · rintro ⟨i, hi1, hi2, rfl⟩
          rw [show i = 0 from by omega]
          rfl
        · rintro rfl
          exact ⟨0, by omega, rfl⟩
      rw [h0, Set.singleton_union,
        Set.insert_eq_of_mem (p2g_CENTER_IN_VORONOI_CELL V y).1,
        (p2g_CONVEX_VORONOI_CLOSED V y).convexHull_eq]
    · have hempty : Finset.Icc j (j - 1) = ∅ := Finset.Icc_eq_empty_iff.2 (by omega)
      have himge : {omegaListN V ul i | i ∈ Finset.Icc j (j - 1)} = (∅ : Set V3) := by
        rw [hempty]
        ext z
        simp
      rw [himge, Set.empty_union, (p2g_CONVEX_VORONOI_LIST V ul).convexHull_eq]
  -- step k→k+1：(A) p2g_union_split 重排 → (B) stepB 壳-窗 rearrange →
  -- omega-窗 vl↔wl 逐点一致（OMEGA_LIST_N_LEMMA）→ p2g_convexHull_sUnion_left
  -- （星引理；非空=BARV_EXISTS，凸性=ℂ-并=p2g_gltvhum_union_g+CONVEX_VORONOI_LIST）
  -- → p2g_sUnion_image_image（𝒞-重指标）→ 归纳假设。
  have hstep : ∀ k : ℕ, j ≤ k → k + 1 ≤ 3 →
      (voronoiList V ul =
        ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (k - 1)} ∪
          voronoiList V vl) | vl ∈ {vl : List V3 |
          barV V k vl ∧ truncateSimplex j vl = ul}}) →
      (voronoiList V ul =
        ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j k} ∪
          voronoiList V vl) | vl ∈ {vl : List V3 |
          barV V (k + 1) vl ∧ truncateSimplex j vl = ul}}) := by
    intro k hjk hk2 ih
    have hk3 : k < 3 := by omega
    -- (B) `hull (window ∪ cell) = hull (window' ∪ hull (ω_k insert cell))`
    have stepB : ∀ v : List V3,
        convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j k} ∪ voronoiList V v) =
        convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j (k - 1)} ∪
          convexHull ℝ (insert (omegaListN V v k) (voronoiList V v))) := by
      intro v
      rw [p2g_convexHull_union_hull, Set.insert_eq, ← Set.union_assoc,
        ← p2g_image_Icc_succ (omegaListN V v) j k hjk]
    -- (C)+(D) hinner：对固定 wl（barV V k wl），`vl`-族的并 = S_wl 的壳。
    have wl2 : ∀ wl : List V3, barV V k wl →
        ⋃₀ {convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j k} ∪ voronoiList V v) |
            v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}} =
        convexHull ℝ ({omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} ∪
          voronoiList V wl) := by
      intro wl hbw
      have hkC := p2g_gltvhum_union_g V wl k hP hs hk3 hbw
      obtain ⟨v0, hv0, hv0t⟩ := p2g_BARV_EXISTS V wl k hP hs hk3 hbw
      have hne : ({convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)) |
          v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}} :
            Set (Set V3)).Nonempty :=
        ⟨convexHull ℝ (insert (omegaListN V v0 k) (voronoiList V v0)),
          ⟨v0, ⟨hv0, hv0t⟩, rfl⟩⟩
      have hconv : Convex ℝ (⋃₀ {convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)) |
          v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}}) := by
        rw [hkC]
        exact p2g_CONVEX_VORONOI_LIST V wl
      have hstar := p2g_convexHull_sUnion_left
        {omegaListN V wl i | i ∈ Finset.Icc j (k - 1)}
        {convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)) |
          v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}}
        hne hconv
      have hpt : ∀ v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl},
          convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j k} ∪ voronoiList V v) =
          convexHull ℝ ({omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} ∪
            convexHull ℝ (insert (omegaListN V v k) (voronoiList V v))) := by
        intro v hv
        obtain ⟨hb, htk⟩ := hv
        have hlen : v.length = k + 2 := hb.1
        rw [stepB v]
        have hom : ∀ i, j ≤ i → i ≤ k - 1 → omegaListN V v i = omegaListN V wl i := by
          intro i hi1 hi2
          have h5 := p2g_OMEGA_LIST_N_LEMMA V v i (k - i) (by omega)
          rw [show i + (k - i) = k from by omega] at h5
          rw [htk] at h5
          exact h5
        have himg : {omegaListN V v i | i ∈ Finset.Icc j (k - 1)} =
            {omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} := by
          ext z
          simp only [Set.mem_setOf_eq, Finset.mem_Icc]
          constructor
          · rintro ⟨i, hi, rfl⟩
            refine ⟨i, hi, ?_⟩
            rw [hom i hi.1 hi.2]
          · rintro ⟨i, hi, rfl⟩
            refine ⟨i, hi, ?_⟩
            rw [hom i hi.1 hi.2]
        rw [himg]
      exact (p2g_sUnion_image_congr hpt).trans
        ((p2g_sUnion_image_image
            (F := {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl})
            (fun v => convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)))
            (fun c => convexHull ℝ ({omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} ∪ c))).trans
          (hstar.symm.trans (by rw [hkC])))
    -- (A) 拆分后逐 wl 套 wl2，收回归纳假设。
    rw [p2g_union_split V ul j k hjk
      (fun vl => convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j k} ∪
        voronoiList V vl))]
    refine ih.trans (p2g_sUnion_image_congr ?_).symm
    intro wl hwl
    obtain ⟨hbw, -⟩ := hwl
    exact wl2 wl hbw
  ext k
  constructor
  · rintro ⟨hk, -⟩
    exact hk
  · intro hk
    have hkle : j ≤ k ∧ k ≤ 3 := Finset.mem_Icc.1 (Finset.mem_coe.1 hk)
    exact p2g_NUMSEG_SUBSET_INDUCT
      (fun k : ℕ => k ∈ (Finset.Icc j 3 : Set ℕ) ∧
        voronoiList V ul =
          ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (k - 1)} ∪
            voronoiList V vl) | vl ∈ {vl : List V3 |
            barV V k vl ∧ truncateSimplex j vl = ul}})
      j 3
      ⟨Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨le_refl j, Nat.le_of_lt hj⟩), hbase⟩
      (fun k hk1 hk2 hmem =>
        ⟨Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨Nat.le_succ_of_le hk1, hk2⟩),
          hstep k hk1 hk2 hmem.2⟩)
      (Set.mem_Icc.2 hkle)

/-! ### §6 新小件：rogers 窗引理 + 辅助

（本节原有的 `p2g_sSup_mem_closed` / `p2g_two_distinct_of_affDim_pos` /
`p2g_mem_hull_insert_facet` / `p2g_union_convex_hull_facets` 四件与 §4 逐字节
重复，重启后清理波删除，统一用 §4 正本。）-/

/-- pack3.hl:1727 `BARV_0` 的诚实重证（PA6 私件 `p6_barV_0` 同法，PA5 正本
BARV_0 为 sorry）。PA5/PA6 正本落地，本为链复制。 -/
private theorem p2g_barV_0 (V : Set V3) (hP : Packing V) (v : V3) (hv : v ∈ V) :
    barV V 0 [v] := by
  refine ⟨by simp, ?_⟩
  rintro wl ⟨⟨yl, heq⟩, hpos⟩
  have hlen : wl.length + yl.length = 1 := by
    rw [← List.length_append, ← heq]; simp
  have hylen : yl.length = 0 := by omega
  have hyl : yl = [] := List.length_eq_zero_iff.mp hylen
  rw [hyl, List.append_nil] at heq
  subst heq
  refine ⟨by simp, ?_, ?_⟩
  · intro z hz
    have hz' : z = v := by simpa [setOfList] using hz
    rw [hz']
    exact hv
  · rw [p2g_VORONOI_LIST_SING]
    have hd3 := p2g_AFF_DIM_VORONOI_CLOSED V v hP
    simp only [List.length_cons, List.length_nil]
    omega

/-- affDim = 0 的非空集是单点（HOL pack1.hl `AFF_DIM_EQ_0` 的本方向）。 -/
private theorem p2g_affDim_eq_zero_singleton {s : Set V3} (hs : affDim s = 0)
    (hne : s.Nonempty) : ∃ a : V3, s = {a} := by
  have hne' : s ≠ ∅ := Set.nonempty_iff_ne_empty.mp hne
  obtain ⟨a, ha⟩ := hne
  have hfr : (Module.finrank ℝ (vectorSpan ℝ s) : ℤ) = 0 := by
    rw [affDim, if_neg hne'] at hs
    omega
  have hbot : vectorSpan ℝ s = ⊥ := by
    have h0 : (Module.finrank ℝ (vectorSpan ℝ s) : ℕ) = 0 := by omega
    haveI hsub : Subsingleton (vectorSpan ℝ s) := Module.finrank_zero_iff.1 h0
    refine Submodule.eq_bot_iff _ |>.2 fun z hz => ?_
    exact congrArg Subtype.val (Subsingleton.elim (α := vectorSpan ℝ s) ⟨z, hz⟩ 0)
  have hsub : ∀ z ∈ s, z - a = (0 : V3) := by
    intro z hz
    have hgen : z - a ∈ (vectorSpan ℝ s : Submodule ℝ V3) := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ ha]
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    rw [hbot] at hgen
    exact (Submodule.mem_bot ℝ).1 hgen
  refine ⟨a, ?_⟩
  ext z
  constructor
  · intro hz
    have h0 := hsub z hz
    simpa using sub_eq_zero.1 h0
  · intro hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ha

/-- 新小件（HOL Rogers.hl:1170-1225 原型）：`barV V 3 vl` 时顶窗 ∪ 胞的壳就是
rogers 单纯形——维数 0 ⇒ 胞 = {ω 3}（`AFF_DIM_VORONOI_LIST` 3 3 + 单点化 +
`TRUNCATE_SIMPLEX_REFL`）。 -/
private theorem p2g_rogers_window (V : Set V3) (vl : List V3) (hbar : barV V 3 vl) :
    convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 0 2} ∪ voronoiList V vl) =
      rogers V vl := by
  have hlen : vl.length = 4 := hbar.1
  have hdim : affDim (voronoiList V vl) = 0 := by
    rw [p2g_AFF_DIM_VORONOI_LIST V vl 3 hbar]
    omega
  have hcell : voronoiList V vl = {omegaListN V vl 3} := by
    obtain ⟨a, ha⟩ := p2g_affDim_eq_zero_singleton hdim
      (by
        have hne := p2g_BARV_IMP_VORONOI_LIST_NOT_EMPTY V vl 3 hbar
        exact Set.nonempty_iff_ne_empty.mpr hne)
    have h3 : omegaListN V vl 3 ∈ voronoiList V vl := by
      have h1 := p2g_OMEGA_LIST_N_IN_VORONOI_LIST V vl 3 3 hbar (le_refl 3)
      rwa [p2g_TRUNCATE_SIMPLEX_REFL 3 vl hbar.1] at h1
    rw [ha] at h3
    rw [ha, Set.mem_singleton_iff.1 h3]
  have himg : ({omegaListN V vl i | i ∈ Finset.Icc 0 2} ∪ {omegaListN V vl 3} : Set V3) =
      omegaListN V vl '' {j : ℕ | j < 4} := by
    ext z
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_setOf_eq]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by have h := Finset.mem_Icc.1 hi; omega, rfl⟩
      · exact ⟨3, by omega, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rcases eq_or_ne x 3 with rfl | hx3
      · exact Or.inr rfl
      · exact Or.inl ⟨x, Finset.mem_Icc.2 ⟨by omega, by omega⟩, rfl⟩
  rw [hcell, himg]
  rw [rogers, hlen]

/-! ## pack_concl.hl: conclusion statements (proofs `by sorry`) -/

/-- HOL `GLTVHUM_concl` (pack_concl.hl:17-19): the closed Voronoi cell of
`u0` is covered by the Rogers simplices rooted at `u0`. -/
theorem GLTVHUM_concl : ∀ (V : Set V3) (u0 p : V3), Packing V ∧ saturated V → u0 ∈ V →
    (p ∈ voronoiClosed V u0 ↔
      ∃ vl : List V3, barV V 3 vl ∧ p ∈ rogers V vl ∧ truncateSimplex 0 vl = [u0]) := by
  -- NEEDS: 非 OAPVION 型 epsilon 唯一性桥，circumcenter 配方不适用（HOL 原证
  -- Rogers.hl:1152 经 Rogers.hl:826 GLTVHUM_lemma1 的 k-归纳 + Voronoi facet 分解）。
  -- 状态（GIANT 移植波 2026-09-28）：五级链下三级已在 PA6 闭合——①
  -- FACET_OF_POLYHEDRON_EXPLICIT_BIS（PA6:286，经 Polytope.FACET_OF_POLYHEDRON_
  -- EXPLICIT + HALFSPACE_EQ_BIS_LE 半空间化）、② IDBEZAL（PA6:349，经
  -- VORONOI_BARV_CANONICAL + VORONOI_LIST_INTER_BIS + KHEJKCI_GEN 双向）、③
  -- VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS（PA6:424，经边界点引理
  -- p6_mem_hull_insert_facet：polyhedron 的 RELATIVE_INTERIOR_OF_POLYHEDRON +
  -- 紧集射线-sup 参数替代 POLYTOPE_UNION_CONVEX_HULL_FACETS 的移植）。
  -- 剩余：④ GLTVHUM_lemma1 已闭合（PA6:869 真证），PA2 侧链复制副本
  -- p2g_GLTVHUM_lemma1 已随 GLTVHUM ⑤ 装配波（2026-09-30）修复闭合（本文件
  -- §5；配套 §0-§6 kit 一并链复制，5 枚上游 sorry 桩见各件 NEEDS 记账：
  -- VORONOI_LIST_CANONICAL / HALFSPACE_EQ / POLYHEDRON_VORONOI_LIST /
  -- POLYTOPE_VORONOI_LIST / BARV_EXISTS）。
  -- 仍剩：⑤ 本桥装配——非 OAPVION 型 epsilon 唯一性桥，circumcenter 配方
  -- 不适用；⑤ 闭合即解锁 PA6:690 GLTVHUM（背引用本桥）与 PA4 cellParams
  -- 唯一性族 9 枚。
  sorry

/-- HOL `DUUNHOR_concl` (pack_concl.hl:21-23): distinct Rogers simplices
meet in a coplanar set. -/
theorem DUUNHOR_concl : ∀ (V : Set V3) (ul vl : List V3), Packing V → saturated V →
    barV V 3 ul → barV V 3 vl → rogers V ul ≠ rogers V vl →
    Coplanar (rogers V ul ∩ rogers V vl) := by
  -- NEEDS: HOL 本体 Rogers.hl:1682-~2450（~770 行，两个 num_WF 强归纳 + 大段凸组合
  -- 比较）为 GIANT；依赖 ROGERS_AFF_DIM_FULL（PA6:763 未证）、POLYHEDRON_VORONOI_LIST
  -- （PA5:1454 未证）、OMEGA_LIST_N_LEMMA（PA5:1502 未证）；PA6:841 DUUNHOR 亦为本桥
  -- 背引用。陈述分歧 r2 裁决(提案官 2026-09-28)：本桥原无 Packing/saturated 前提，
  -- 而 HOL 证明第一步即经 VORONOI_CLOSED_EQ_LEMMA（Rogers.hl:1256，带 packing
  -- 前提）消费 packing——PA6:837 "前提未用" 注记与 HOL 原文不符。按 DECISIONS
  -- 2026-09-28 授权走保真对齐：本陈述已补 Packing V ∧ saturated V，PA6:841
  -- 背引用已同步加参（无前提版反例构造可行——两簇远距 barV 3 四面体，V 取 8 点
  -- 显式集，机器化成本高未收口，见提案项 13 (b)）。affDim≤2 的退化分支机械
  -- （PA6:707 可引），卡的是双满维主情形。三前件复核（GIANT 移植波
  -- 2026-09-28）：ROGERS_AFF_DIM_FULL（PA6:577）、POLYHEDRON_VORONOI_LIST
  -- （PA5:1501）、OMEGA_LIST_N_LEMMA（PA5:1551）三者均仍为 sorry——本桥本轮
  -- 不做，待上三件 + GLTVHUM_concl 闭合后另开移植波。
  sorry

/-- HOL `QXSKIIT_concl` (pack_concl.hl:25-28): unique interpolation on the
affine hull. (HL states this over `real^N`; ported over `V3`.) -/
theorem QXSKIIT_concl : ∀ {A : Type} (vf : A → V3) (b : A → ℝ),
    (vf '' (Set.univ : Set A)).Finite → ¬affineDependent (vf '' (Set.univ : Set A)) →
    (∀ i j : A, vf i = vf j → b i = b j) →
    ∃! p : V3, p ∈ (affineSpan ℝ (vf '' (Set.univ : Set A)) : Set V3) ∧
      ∀ i j : A, p ⬝ᵥ (vf i - vf j) = b i - b j := by
  sorry

/-- 辅助引理（本波新增，`_p2` 后缀，statement 冻结纪律见任务书）：Mathlib
`AffineIndependent.existsUnique_dist_eq` 桥——非空仿射无关点集在仿射包上有
唯一的等距点，且 `circumcenter`/`radV` 两个 `Classical.epsilon` 恰好选中它。
这是 HOL Rogers.hl:3816 `CIRCUMCENTER_LEMMA` 的完整复刻，用于清偿
`OAPVION{1,2,3}_concl` 三座 pack_concl 桥。 -/
private theorem circumcenterRadVUnique_p2 (S : Set V3) (hne : S.Nonempty)
    (hind : ¬affineDependent S) :
    ∃ q : V3, circumcenter S = q ∧ q ∈ (affineSpan ℝ S : Set V3) ∧
      (∀ z ∈ S, radV S = dist q z) ∧
      (∀ q' : V3, q' ∈ (affineSpan ℝ S : Set V3) →
        (∃ c : ℝ, ∀ z ∈ S, dist q' z = c) → q' = q) := by
  haveI : Nonempty ↥S := hne.to_subtype
  have hai : AffineIndependent ℝ (fun x : S => (x : V3)) := by
    rw [affineDependent, not_not] at hind
    exact hind
  haveI : Finite ↥S :=
    haveI : FiniteDimensional ℝ V3 := inferInstance
    finite_of_fin_dim_affineIndependent ℝ hai
  have hrange : Set.range (fun x : S => (x : V3)) = S := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨cs, ⟨hcmem, hcontains⟩, hcsuniq⟩ := hai.existsUnique_dist_eq
  rw [hrange] at hcmem hcontains
  have hdist : ∀ z ∈ S, dist z cs.center = cs.radius := fun z hz => hcontains hz
  have hdist' : ∀ z ∈ S, cs.radius = dist cs.center z := fun z hz => by
    rw [dist_comm]
    exact (hdist z hz).symm
  have hccp : circumcenter S = cs.center := by
    have hcpred : (circumcenter S) ∈ (affineSpan ℝ S : Set V3) ∧
        ∃ c : ℝ, ∀ z ∈ S, c = dist (circumcenter S) z :=
      Classical.epsilon_spec
        (p := fun v : V3 => v ∈ (affineSpan ℝ S : Set V3) ∧ ∃ c : ℝ, ∀ z ∈ S, c = dist v z)
        ⟨cs.center, hcmem, cs.radius, hdist'⟩
    obtain ⟨hcpred1, c₀, hc₀⟩ := hcpred
    have heq : EuclideanGeometry.Sphere.mk (circumcenter S) c₀ = cs := by
      refine hcsuniq _ ⟨?_, ?_⟩
      · rw [hrange]
        exact hcpred1
      · intro x hx
        obtain ⟨z, rfl⟩ := hx
        show dist (z : V3) (circumcenter S) = c₀
        rw [hc₀ z z.2, dist_comm]
    exact congrArg EuclideanGeometry.Sphere.center heq
  have hrad : radV S = cs.radius := by
    obtain ⟨z0, hz0⟩ := hne
    have hspec : ∀ z ∈ S, radV S = dist (circumcenter S) z :=
      Classical.epsilon_spec
        (p := fun c : ℝ => ∀ z ∈ S, c = dist (circumcenter S) z)
        ⟨cs.radius, fun z hz => by rw [hccp]; exact hdist' z hz⟩
    have h1 := hspec z0 hz0
    rw [hccp, dist_comm] at h1
    exact h1.trans (hdist z0 hz0)
  refine ⟨cs.center, hccp, hcmem, fun z hz => hrad.trans (hdist' z hz), ?_⟩
  rintro q' hqm' ⟨c', hc'⟩
  have heq : EuclideanGeometry.Sphere.mk q' c' = cs := by
    refine hcsuniq _ ⟨?_, ?_⟩
    · rw [hrange]
      exact hqm'
    · intro x hx
      obtain ⟨z, rfl⟩ := hx
      rw [Metric.mem_sphere]
      exact (dist_comm (z : V3) q').trans (hc' z z.2)
  exact congrArg EuclideanGeometry.Sphere.center heq

/-- HOL `OAPVION1_concl` (pack_concl.hl:35-36): the circumcenter lies on the
affine hull. -/
theorem OAPVION1_concl : ∀ S : Set V3, S ≠ ∅ → ¬affineDependent S →
    circumcenter S ∈ (affineSpan ℝ S : Set V3) := by
  intro S h1 h2
  obtain ⟨q, hccp, hqm, -, -⟩ :=
    circumcenterRadVUnique_p2 S (Set.nonempty_iff_ne_empty.mpr h1) h2
  rw [hccp]
  exact hqm

/-- HOL `OAPVION2_concl` (pack_concl.hl:38-39): all points are at
circumradius distance from the circumcenter. -/
theorem OAPVION2_concl : ∀ S : Set V3, ¬affineDependent S →
    ∀ w ∈ S, radV S = dist (circumcenter S) w := by
  intro S h2 w hw
  obtain ⟨q, hccp, -, hd, -⟩ := circumcenterRadVUnique_p2 S ⟨w, hw⟩ h2
  rw [hccp]
  exact hd w hw

/-- HOL `OAPVION3_concl` (pack_concl.hl:41-42): characterization of the
circumcenter by equidistance on the affine hull. -/
theorem OAPVION3_concl : ∀ S : Set V3, ¬affineDependent S →
    ∀ p : V3, p ∈ (affineSpan ℝ S : Set V3) → (∃ c : ℝ, ∀ w ∈ S, dist p w = c) →
      p = circumcenter S := by
  intro S h2 p hspan hc
  obtain ⟨c, hc⟩ := hc
  by_cases hse : S = ∅
  · subst hse
    have hb : (affineSpan ℝ (∅ : Set V3)) = ⊥ :=
      (affineSpan_eq_bot (k := ℝ)).2 rfl
    rw [hb] at hspan
    exact absurd hspan (AffineSubspace.notMem_bot ℝ V3 p)
  · obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hse
    obtain ⟨q, hccp, -, -, hu⟩ := circumcenterRadVUnique_p2 S ⟨w, hw⟩ h2
    exact (hu p hspan ⟨c, hc⟩).trans hccp.symm

/-- HOL `MHFTTZN1_concl` (pack_concl.hl:44-45): the points of a `barV V k`
list span dimension exactly `k`. -/
theorem MHFTTZN1_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
    Packing V → barV V k ul → affDim (setOfList ul) = (k : ℤ) := by
  sorry

/-- HOL `MHFTTZN2_concl` (pack_concl.hl:47-48): the affine hull of the
Voronoi face dual to `ul` is the intersection of the bisectors through
`HD ul`. -/
theorem MHFTTZN2_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
    Packing V → barV V k ul →
    ∀ p : V3, p ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) ↔
      ∀ u ∈ setOfList ul, p ∈ bis (hdV ul) u := by
  sorry

/-- HOL `MHFTTZN3_concl` (pack_concl.hl:50-52). -/
theorem MHFTTZN3_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
    Packing V → barV V k ul →
    ((affineSpan ℝ (voronoiList V ul) : Set V3) ∩
        (affineSpan ℝ (setOfList ul) : Set V3)) =
      {circumcenter (setOfList ul)} := by
  sorry

/-- HOL `MHFTTZN4_concl` (pack_concl.hl:54-56): the circumcenter sees the
two affine hulls orthogonally. -/
theorem MHFTTZN4_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ) (u v q : V3), k ≤ 3 →
    saturated V → Packing V → barV V k ul → q = circumcenter (setOfList ul) →
    u ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) →
    v ∈ (affineSpan ℝ (setOfList ul) : Set V3) →
    (u - q) ⬝ᵥ (v - q) = 0 := by
  sorry

/-- HOL `XYOFCGX_concl` (pack_concl.hl:61-64): a point of `V \ S` is farther
from the circumcenter than every point of `S` once the circumradius is below
`sqrt 2`. -/
theorem XYOFCGX_concl : ∀ (V S : Set V3) (p : V3), S ⊆ V → ¬affineDependent S →
    p = circumcenter S → radV S < Real.sqrt 2 →
    ∀ u v : V3, u ∈ S → v ∈ V \ S → dist v p > dist u p := by
  sorry

/-- HOL `XNHPWAB1_concl` (pack_concl.hl:66-68): below `sqrt 2` the omega
point is the circumcenter. -/
theorem XNHPWAB1_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
    omegaList V ul = circumcenter (setOfList ul) := by
  sorry

/-- HOL `XNHPWAB2_concl` (pack_concl.hl:70-72). -/
theorem XNHPWAB2_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
    omegaList V ul ∈ convexHull ℝ (setOfList ul) := by
  sorry

/-- HOL `XNHPWAB3_concl` (pack_concl.hl:80-82, active version). -/
theorem XNHPWAB3_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
    affDim {omegaListN V ul j | j ∈ Finset.Icc 0 k} = (k : ℤ) := by
  sorry

/-- HOL `XNHPWAB4_concl` (pack_concl.hl:84-86): the truncated circumradii
increase strictly. -/
theorem XNHPWAB4_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
    ∀ i j : ℕ, i < j → j ≤ k →
      hl (truncateSimplex i ul) < hl (truncateSimplex j ul) := by
  sorry

/-- HOL `WAUFCHE1_concl` (pack_concl.hl:89-91). -/
theorem WAUFCHE1_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → barV V k ul → hl ul ≤ dist (omegaList V ul) (hdV ul) := by
  sorry

/-- HOL `WAUFCHE2_concl` (pack_concl.hl:93-95). -/
theorem WAUFCHE2_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → barV V k ul → hl ul < Real.sqrt 2 →
    hl ul = dist (omegaList V ul) (hdV ul) := by
  sorry

/-- HOL `YIFVQDV_concl` (pack_concl.hl:100-102): barV-ness and the omega
point are invariant under permuting the list. -/
theorem YIFVQDV_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ) (p : Equiv.Perm ℕ),
    Packing V → saturated V → barV V k ul → hl ul < Real.sqrt 2 →
    permutes p (Set.Icc 0 k) →
    barV V k (leftActionList p ul) ∧
      omegaList V (leftActionList p ul) = omegaList V ul := by
  sorry

/-- HOL `KSOQKWL_concl` (pack_concl.hl:104-105): Rogers uniqueness forces
the identity permutation. -/
theorem KSOQKWL_concl : ∀ (V : Set V3) (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ),
    saturated V → Packing V → barV V k ul → hl ul < Real.sqrt 2 →
    permutes p (Set.Icc 0 k) →
    rogers V ul = rogers V (leftActionList p ul) → p = Equiv.refl ℕ := by
  sorry

/-- HOL `IVFICRK_concl` (pack_concl.hl:110-113): an explicit bijection
giving the action of a permutation on the list with one element dropped.
(HL leaves `i σ` free inside the second conjunct — implicitly generalized;
bound explicitly here. Generic in the element type `A`, as in HL.) -/
theorem IVFICRK_concl : ∀ {A : Type} [Inhabited A] (k : ℕ),
    ∃ g : ℕ × Equiv.Perm ℕ → Equiv.Perm ℕ,
      Set.BijOn g {q : ℕ × Equiv.Perm ℕ | q.1 ∈ Set.Icc 0 (k + 1) ∧
          permutes q.2 (Set.Icc 0 k)}
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k + 1))} ∧
      ∀ (ul : List A) (i : ℕ) (σ : Equiv.Perm ℕ) (j : ℕ), ul.length = k + 2 →
        j ≤ k →
        (leftActionList (g (i, σ)) ul).getD j default =
          (leftActionList σ (dropIth ul i)).getD j default := by
  sorry

/-- HOL `WQPRRDY_concl` (pack_concl.hl:115-117): the hull of the simplex is
the union of the Rogers simplices over all orderings. -/
theorem WQPRRDY_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → barV V k ul → hl ul < Real.sqrt 2 →
    convexHull ℝ (setOfList ul) =
      ⋃₀ ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 k)}) := by
  sorry

/-- HOL `MXI_EXISTS_concl` (pack_concl.hl:120-123). -/
theorem MXI_EXISTS_concl : ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
    barV V 3 ul → Real.sqrt 2 ≤ hl ul →
    mxi V ul ∈ convexHull ℝ {omegaListN V ul 2, omegaListN V ul 3} ∧
      dist (mxi V ul) (hdV ul) = Real.sqrt 2 := by
  sorry

/-- HOL `EMNWUUS1_concl` (pack_concl.hl:128-129). -/
theorem EMNWUUS1_concl : ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
    barV V 3 ul → (hl ul < Real.sqrt 2 ↔ mcell4 V ul ≠ ∅) := by
  sorry

/-- HOL `EMNWUUS2_concl` (pack_concl.hl:131-133). -/
theorem EMNWUUS2_concl : ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
    barV V 3 ul →
    (hl ul < Real.sqrt 2 ↔
      mcell0 V ul = ∅ ∧ mcell1 V ul = ∅ ∧ mcell2 V ul = ∅ ∧ mcell3 V ul = ∅) := by
  sorry

/-- HOL `SLTSTLO1_concl` (pack_concl.hl:135-136): the Rogers simplex is
covered by the cells `mcell 0..4`. -/
theorem SLTSTLO1_concl : ∀ (V : Set V3) (ul : List V3) (p : V3), saturated V →
    Packing V → barV V 3 ul → p ∈ rogers V ul →
    ∃ i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul := by
  sorry

/-- HOL `SLTSTLO2_concl` (pack_concl.hl:138-139): away from a null set the
covering is unique. -/
theorem SLTSTLO2_concl : ∀ (V : Set V3) (ul : List V3),
    ∃ Z : Set V3, ∀ p : V3, saturated V → Packing V → barV V 3 ul →
      nullSet Z ∧ (p ∈ rogers V ul \ Z → ∃! i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul) := by
  sorry

/-- HOL `RVFXZBU1_concl` (pack_concl.hl:141-143): intersections of cells
from different lists are null. -/
theorem RVFXZBU1_concl : ∀ (V : Set V3) (ul vl : List V3) (i j : ℕ), saturated V →
    Packing V → barV V 3 ul → barV V 3 vl → i ≠ j →
    nullSet (mcell i V ul ∩ mcell j V vl) := by
  sorry

/-- HOL `RVFXZBU2_concl` (pack_concl.hl:145-147): non-null overlap of
same-index cells forces a permutation. -/
theorem RVFXZBU2_concl : ∀ (V : Set V3) (ul vl : List V3) (i : ℕ), saturated V →
    Packing V → barV V 3 ul → barV V 3 vl →
    ¬nullSet (mcell i V ul ∩ mcell i V vl) →
    ∃ p : Equiv.Perm ℕ, permutes p (Set.Icc 0 (i - 1)) ∧ vl = leftActionList p ul := by
  sorry

/-- HOL `RVFXZBU3_concl` (pack_concl.hl:149-150). ENCODING-FIX 2026-09-19
(mirror of the PackingAuto10 ruling): HOL `permutes` is complement-fixing,
so the faithful Lean form carries the tail-fixedness side condition
explicitly; the weak pointwise `permutes` hypothesis alone would make the
statement false (transposition counterexample). -/
theorem RVFXZBU3_concl : ∀ (V : Set V3) (ul : List V3) (i : ℕ) (p : Equiv.Perm ℕ),
    saturated V → Packing V → barV V 3 ul → permutes p (Set.Icc 0 (i - 1)) →
    (∀ j : ℕ, i ≤ j → p j = j) →
    mcell i V (leftActionList p ul) = mcell i V ul := by
  sorry

/-- HOL `LEPJBDJ_concl` (pack_concl.hl:152-155): the packing points of a
cell are the first `k` list points. -/
theorem LEPJBDJ_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → barV V 3 ul → 1 ≤ k → k ≤ 4 → mcell k V ul ≠ ∅ →
    V ∩ mcell k V ul = setOfList (truncateSimplex (k - 1) ul) := by
  sorry

/-- HOL `LEPJBDJ_0_concl` (pack_concl.hl:157-162). -/
theorem LEPJBDJ_0_concl : ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
    barV V 3 ul → V ∩ mcell 0 V ul = ∅ := by
  sorry

/-- HOL `HDTFNFZ_concl` (pack_concl.hl:164-170): for non-null cells,
`VX` is the intersection with the packing. -/
theorem HDTFNFZ_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3) (X : Set V3),
    saturated V → Packing V → barV V 3 ul → X = mcell k V ul → ¬nullSet X →
    VX V X = V ∩ X := by
  sorry

/-- HOL `URRPHBZ1_concl` (pack_concl.hl:172-174): cells are measurable. -/
theorem URRPHBZ1_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
    Packing V → barV V 3 ul → MeasurableSet (mcell k V ul) := by
  sorry

/-- HOL `URRPHBZ2_concl` (pack_concl.hl:176-178): cells are eventually
radial at packing points. -/
theorem URRPHBZ2_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3),
    saturated V → Packing V → barV V 3 ul → v ∈ V →
    EventuallyRadial v (mcell k V ul) := by
  sorry

/-- HOL `URRPHBZ3_concl` (pack_concl.hl:180-183): away from the packing
vertices, a non-null cell has positive clearance. -/
theorem URRPHBZ3_concl : ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3),
    saturated V → Packing V → barV V 3 ul → ¬nullSet (mcell k V ul) →
    v ∈ V \ VX V (mcell k V ul) →
    ∃ t : ℝ, t > 0 ∧ ∀ p ∈ mcell k V ul, t < dist p v := by
  sorry

/-- HOL `QZYZMJC_concl` (pack_concl.hl:185-187): the solid angles around a
packing point sum to `4π`. -/
theorem QZYZMJC_concl : ∀ (V : Set V3) (v : V3), saturated V → Packing V → v ∈ V →
    setSum {X | mcellSet V X ∧ v ∈ VX V X} (fun t => sol v t) = 4 * Real.pi := by
  sorry

/-- HOL `KIZHLTL1_concl` (pack_concl.hl:201-203). -/
theorem KIZHLTL1_concl : ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
    1 ≤ r →
    setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} volume.real +
        c * r ^ 2 ≤
      setSum (V ∩ Metric.ball 0 r) (fun u => volume.real (voronoiOpen V u)) := by
  sorry

/-- HOL `KIZHLTL2_concl` (pack_concl.hl:205-208). -/
theorem KIZHLTL2_concl : ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
    1 ≤ r →
    ((Nat.card ((V ∩ Metric.ball 0 r : Set V3)) : ℕ) : ℝ) * 8 * mm1 + c * r ^ 2 ≤
      (2 * mm1 / Real.pi) *
        setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V) := by
  sorry

/-- HOL `KIZHLTL3_concl` (pack_concl.hl:210-220). -/
theorem KIZHLTL3_concl : ∀ (V : Set V3) (f : ℝ → ℝ), ∃ c : ℝ, ∀ r : ℝ,
    saturated V → Packing V → 1 ≤ r →
    (∃ c1 : ℝ, ∀ x : ℝ, 2 ≤ x ∧ x < Real.sqrt 8 → |f x| ≤ c1) →
    ((8 * mm2 / Real.pi) *
          setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
            (fun X => setSum (edgeX V X) fun e =>
              let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
              dihX V X (q.1, q.2) * f (hl [q.1, q.2]))
        + c * r ^ 2 ≤
      8 * mm2 * setSum (V ∩ Metric.ball 0 r)
        (fun u => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v < Real.sqrt 8}
          (fun v => f (hl [u, v])))) := by
  sorry

/-- HOL `OXLZLEZ_concl` (pack_concl.hl:222). -/
theorem OXLZLEZ_concl : ∀ V : Set V3, saturated V → Packing V →
    cellClusterInequality V := by
  sorry

/-- HOL `TSKAJXY_statement` (pack_concl.hl:224-231, a `new_definition` of a
proposition). -/
def TSKAJXY_statement : Prop :=
  ∀ (V : Set V3) (X : Set V3), saturated V → Packing V → mcellSet V X →
    criticalEdgeX V X = ∅ → gammaX V X lmfun ≥ 0

/-- HOL `UPFZBZM_concl` (pack_concl.hl:233-237). -/
theorem UPFZBZM_concl : ∀ V : Set V3, saturated V → Packing V →
    cellClusterInequality V → TSKAJXY_statement → lmfunInequality V →
    ∃ G : V3 → ℝ, negligibleFun0 G V ∧ fccCompatible G V := by
  sorry

/-! ### RDWKARC_concl 支撑件（本波新增，`_p2` 后缀；对应 RDWKARC.hl 的
translation/re-index 小引理组，证明形态逐条对照 PackingAuto19 的已证版本）-/

/-- HOL `PACKING_TRANS` (RDWKARC.hl:115): packings are translation invariant.
(证明照搬 PackingAuto19.PACKING_TRANS，本文件不能反向 import PA19。) -/
private theorem packingTrans_p2 (V : Set V3) (hV : Packing V) (x : V3) :
    Packing {u : V3 | u + x ∈ V} := by
  intro u hu v hv hlt
  have hd : dist (u + x) (v + x) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm]
    abel
  exact add_right_cancel (hV _ hu _ hv (by rwa [hd]))

/-- HOL `RADV_TRANS_EQ` core (RDWKARC.hl:171): the circumradius of a
two-point set is half the distance. (照搬 PackingAuto19.radV_pair。) -/
private theorem radVPair_p2 (u v : V3) (huv : u ≠ v) :
    radV {u, v} = dist u v / 2 := by
  have hmem : AffineMap.lineMap (k := ℝ) u v (1 / 2) ∈ (affineSpan ℝ {u, v} : Set V3) :=
    AffineMap.lineMap_mem_affineSpan_pair (1 / 2) u v
  have hmd1 : dist u v / 2 = dist (AffineMap.lineMap (k := ℝ) u v (1 / 2)) u := by
    rw [dist_lineMap_left]
    norm_num
    ring
  have hmd2 : dist u v / 2 = dist (AffineMap.lineMap (k := ℝ) u v (1 / 2)) v := by
    rw [dist_lineMap_right]
    norm_num
    ring
  have hwit : ∃ y : V3, y ∈ (affineSpan ℝ {u, v} : Set V3) ∧
      ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3), c = dist y w := by
    refine ⟨AffineMap.lineMap (k := ℝ) u v (1 / 2), hmem, dist u v / 2, fun w hw => ?_⟩
    rcases Set.mem_insert_iff.mp hw with rfl | rfl
    · exact hmd1
    · exact hmd2
  have hcc : (fun v0 : V3 => v0 ∈ (affineSpan ℝ {u, v} : Set V3) ∧
      ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3), c = dist v0 w) (circumcenter {u, v}) :=
    Classical.epsilon_spec hwit
  obtain ⟨hccmem, c₀, hc₀⟩ := hcc
  have hu : u ∈ (affineSpan ℝ {u, v} : Set V3) := mem_affineSpan (k := ℝ) (by simp)
  have hdir : circumcenter {u, v} - u ∈ vectorSpan ℝ {u, v} := by
    have h5 : circumcenter {u, v} -ᵥ u ∈ (affineSpan ℝ {u, v}).direction :=
      AffineSubspace.vsub_mem_direction hccmem hu
    rwa [direction_affineSpan] at h5
  rw [vectorSpan_pair (k := ℝ) u v] at hdir
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hdir
  have ht' : t • (u - v) = circumcenter {u, v} - u := ht
  have hduv : dist u v ≠ 0 := fun hzz => huv (dist_eq_zero.mp hzz)
  have h1 : |t| * dist u v = dist (circumcenter {u, v}) u := by
    rw [dist_eq_norm, dist_eq_norm, ← ht', norm_smul, Real.norm_eq_abs]
  have hv2 : circumcenter {u, v} - v = (t + 1) • (u - v) := by
    rw [show (t + 1) • (u - v) = t • (u - v) + (u - v) from by rw [add_smul, one_smul], ht']
    abel
  have h2 : |t + 1| * dist u v = dist (circumcenter {u, v}) v := by
    rw [dist_eq_norm, dist_eq_norm, hv2, norm_smul, Real.norm_eq_abs]
  have habs : |t| = |t + 1| := by
    have h3 : |t| * dist u v = |t + 1| * dist u v := by
      rw [h1, h2, ← hc₀ _ (Set.mem_insert u {v}),
        ← hc₀ _ (Set.mem_insert_of_mem _ (by simp))]
    exact mul_right_cancel₀ hduv h3
  have hhalf : t = -(1 / 2) := by
    rcases abs_eq_abs.mp habs with h | h
    · linarith
    · linarith
  have hfin : dist (circumcenter {u, v}) u = dist u v / 2 := by
    rw [← h1, hhalf, abs_of_neg (show (0 : ℝ) > -(1 / 2) from by norm_num)]
    ring
  have hQ : (fun c : ℝ => ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter {u, v}) w) (radV {u, v}) :=
    Classical.epsilon_spec
      (p := fun c : ℝ => ∀ w ∈ ({u, v} : Set V3), c = dist (circumcenter {u, v}) w)
      ⟨c₀, hc₀⟩
  rw [hQ u (Set.mem_insert u {v})]
  exact hfin

/-- HOL `RADV_TRANS_EQ` (RDWKARC.hl:171): pair circumradii are translation
invariant. (照搬 PackingAuto19.RADV_TRANS_EQ。) -/
private theorem radVTransEq_p2 (u v x : V3) (h : ¬(u = v)) :
    radV {u, v} = radV {u + x, v + x} := by
  have hd : dist (u + x) (v + x) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm]
    abel
  rw [radVPair_p2 u v (fun huv => h huv),
    radVPair_p2 (u + x) (v + x) (by simp [h]), hd]

/-- Re-index key: `hl [0, a] = hl [u, a + u]` for `a ≠ 0` (RDWKARC.hl 末段的
`hl` translation invariance，经 `set_of_list`/`RADV_TRANS_EQ`)。 -/
private theorem hlPairAdd_p2 {a u : V3} (ha : a ≠ 0) : hl [0, a] = hl [u, a + u] := by
  have hsl : ∀ x y : V3, setOfList [x, y] = {x, y} := by
    intro x y
    ext b
    simp [setOfList]
  have hkey := radVTransEq_p2 (0 : V3) a u (Ne.symm ha)
  rw [zero_add] at hkey
  show radV (setOfList [0, a]) = radV (setOfList [u, a + u])
  rw [hsl, hsl]
  exact hkey

/-- `setSum` respects pointwise congruence of the summand. -/
private theorem setSumCongr_p2 {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ a ∈ s, f a = g a) : setSum s f = setSum s g := by
  by_cases hs : Set.Finite s
  · unfold setSum
    rw [dif_pos hs, dif_pos hs]
    exact Finset.sum_congr rfl fun a ha => h a (hs.mem_toFinset.mp ha)
  · unfold setSum
    rw [dif_neg hs, dif_neg hs]

/-- `setSum` re-indexes along an injective image (SUM_EQ_GENERAL_INVERSES 的
Lean 形；junk 约定两侧同赌有限性)。 -/
private theorem setSumImage_p2 (g : V3 → V3) (A : Set V3) (f : V3 → ℝ)
    (hinj : Set.InjOn g A) (hA : A.Finite) :
    setSum (g '' A) f = setSum A (fun a => f (g a)) := by
  classical
  have himg : (g '' A).Finite := hA.image g
  unfold setSum
  rw [dif_pos himg, dif_pos hA, Set.Finite.toFinset_image g hA himg,
    Finset.sum_image (fun a ha b hb h => hinj (hA.mem_toFinset.mp ha)
      (hA.mem_toFinset.mp hb) h)]

/-- HOL `JGXZYGW_KY` (RDWKARC.hl:76-91): the `JGXZYGW` density bound at the
origin in the `negligible_fun_0` functional form (`negligibleFun0` is by
definition `negligibleFunP _ _ 0`, so this is literally `JGXZYGW` at `p = 0`).

NEEDS (2026-09-29 已清偿): pack1.hl `JGXZYGW` 链现由新叶模块
`Kepler.Text.PackingJGXZYGW` 全真证承载（`jgxzygw_p`，#print axioms 仅标准三；
PA1:1026 骨架的债已被该模块替证）。PA19 侧同件经 private `JGXZYGW_p19` 同源
桥接；PA1 因 `saturated` 公开重名仍不可 import（merge 期裁决见
docs/jgxzygw-scout.md §5）。 -/
private theorem JGXZYGW_KY_p2 (S : Set V3) (hV : Packing S) (hs : saturated S)
    (hA : ∃ A : V3 → ℝ, fccCompatible A S ∧ negligibleFun0 A S) :
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      volume.real ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball (0 : V3) r) /
        volume.real (Metric.ball (0 : V3) r) ≤ Real.pi / Real.sqrt 18 + c / r := by
  -- NEEDS discharged (2026-09-29): PackingJGXZYGW.jgxzygw_p（PA1.JGXZYGW 链
  -- 全真证新叶模块，#print axioms 仅标准三），p = 0 特化 + setSum 桥。
  obtain ⟨A, hfcc, hneg⟩ := hA
  obtain ⟨C, hC0, hC⟩ := hneg
  exact jgxzygw_p S 0 hV hs ⟨A, fun v hv => hfcc v hv, C, hC0,
    fun r hr hfin => by simpa only [setSum, dif_pos hfin] using hC r hr⟩

/-- HOL `RDWKARC_concl` (pack_concl.hl:247-249, modified Dec 31 2012).
证明 = RDWKARC.hl:180-314（去 UPFZBZM/JGXZYGW 两座解析银行）：.unpack
`¬kepler_conjecture` 取反例 `V`；若 `lmfunInequality V`，`UPFZBZM_concl` +
`JGXZYGW_KY_p2` 给出密度上界，矛盾；故存在 `u ∈ V` 使边 lmfun 和 > 12；取
 witness `{v | v + u ∈ V} ∩ ballAnnulus`（PACKING_TRANS + PACKING_SUBSET），
 annulus 和沿 `v ↦ v + u` 重编为 `V`-边和（SUM_EQ_GENERAL_INVERSES，packing
 分离处理 `v = u` junk 情形，`hl` 平移不变性经 `radVPair_p2`）。 -/
theorem RDWKARC_concl : ¬keplerConjecture →
    (∀ V : Set V3, Packing V → saturated V → cellClusterInequality V) →
    TSKAJXY_statement →
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬localAnnulusInequality V := by
  intro hkc hcc hT
  -- RDWKARC.hl:189-193 — unpack `¬kepler_conjecture` to a failing witness.
  obtain ⟨V, hP, hs, hden⟩ : ∃ V : Set V3, Packing V ∧ saturated V ∧
      ¬(∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
        volume.real (((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 r : Set V3)) /
          volume.real (Metric.ball (0 : V3) r) ≤ Real.pi / Real.sqrt 18 + c / r) := by
    by_contra hex
    refine hkc fun V hV => ?_
    by_contra hc
    exact hex ⟨V, hV.1, hV.2, hc⟩
  -- RDWKARC.hl:196-215 — `lmfunInequality V` would give the density bound
  -- via UPFZBZM + JGXZYGW_KY; contradiction.
  have hnlm : ¬lmfunInequality V := by
    intro hlm
    obtain ⟨G, hG0, hGf⟩ := UPFZBZM_concl V hs hP (hcc V hP hs) hT hlm
    exact hden (JGXZYGW_KY_p2 V hP hs ⟨G, hGf, hG0⟩)
  -- RDWKARC.hl:217-222 — extract `u ∈ V` with edge lmfun-sum > 12.
  obtain ⟨u, hu, hsum⟩ : ∃ u : V3, u ∈ V ∧
      12 < setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
        (fun v => lmfun (hl [u, v])) := by
    by_contra hall
    push_neg at hall
    exact hnlm hall
  have hPT : Packing {v : V3 | v + u ∈ V} := packingTrans_p2 V hP u
  -- Membership of the witness in terms of distances (annulus ↔ edge set).
  have hAann : ∀ v : V3, v ∈ {w : V3 | w + u ∈ V} ∩ ballAnnulus →
      v + u ∈ V ∧ dist 0 v ≤ 2 * h0 ∧ 2 ≤ dist 0 v := by
    intro v hv
    rw [Set.mem_inter_iff] at hv
    obtain ⟨hm, hann⟩ := hv
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball] at hann
    refine ⟨hm, ?_, ?_⟩
    · rw [dist_comm]; exact hann.1
    · rw [dist_comm]; exact le_of_not_gt hann.2
  have hballmem : ∀ v : V3, dist 0 v ≤ 2 * h0 → 2 ≤ dist 0 v → v ∈ ballAnnulus := by
    intro v hle h2
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball]
    refine ⟨?_, ?_⟩
    · rw [dist_comm]; exact hle
    · intro hb
      rw [dist_comm] at hb
      exact absurd hb (not_lt.2 h2)
  have hAfin : ({v : V3 | v + u ∈ V} ∩ ballAnnulus).Finite := by
    refine Set.Finite.subset (hPT.finite_inter_ball (2 * h0 + 1)) ?_
    intro v hv
    obtain ⟨hm, hle, -⟩ := hAann v hv
    refine Set.mem_inter hm (Metric.mem_ball.2 ?_)
    rw [dist_comm]
    linarith
  refine ⟨{v : V3 | v + u ∈ V} ∩ ballAnnulus, ?_, Set.inter_subset_right, ?_⟩
  · -- packing of the witness: PACKING_TRANS then PACKING_SUBSET.
    intro a ha b hb hlt
    rw [Set.mem_inter_iff] at ha hb
    exact hPT a ha.1 b hb.1 hlt
  · -- RDWKARC.hl:226-314 — the annulus sum re-indexes to the V-edge sum.
    intro hLAI
    have hinj : Set.InjOn (fun a : V3 => a + u)
        ({v : V3 | v + u ∈ V} ∩ ballAnnulus) := fun _ _ _ _ h => add_right_cancel h
    have hTeq : {v : V3 | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0} =
        (fun a : V3 => a + u) '' ({v : V3 | v + u ∈ V} ∩ ballAnnulus) := by
      ext w
      constructor
      · rintro ⟨hwV, hwu, hdu⟩
        have hdu2 : dist 0 (w - u) = dist u w := by
          rw [dist_eq_norm, dist_eq_norm]; abel
        have h2wu : 2 ≤ dist u w := Packing.dist_ge_two hP hu hwV (Ne.symm hwu)
        have hVin : w - u + u = w := by abel
        have hinV : (w - u) + u ∈ V := by rw [hVin]; exact hwV
        have hle : dist 0 (w - u) ≤ 2 * h0 := by rw [hdu2]; exact hdu
        have h2 : 2 ≤ dist 0 (w - u) := by rw [hdu2]; exact h2wu
        refine ⟨w - u, Set.mem_inter hinV (hballmem _ hle h2), hVin⟩
      · rintro ⟨a, ha, rfl⟩
        show a + u ∈ {v : V3 | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
        obtain ⟨haV, hle, ha2⟩ := hAann a ha
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0] at ha2
          rw [dist_self] at ha2
          linarith
        refine ⟨haV, ?_, ?_⟩
        · intro h
          have h' : a + u = (0 : V3) + u := by rw [zero_add]; exact h
          exact ha0 (add_right_cancel h')
        · have hd : dist u (a + u) = dist 0 a := by
            rw [dist_eq_norm, dist_eq_norm]; abel
          rw [hd]; exact hle
    have key : setSum ({v : V3 | v + u ∈ V} ∩ ballAnnulus)
        (fun w => lmfun (hl [0, w])) =
        setSum {v : V3 | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
          (fun v => lmfun (hl [u, v])) := by
      rw [hTeq, setSumImage_p2 (fun a : V3 => a + u) _ _ hinj hAfin]
      refine setSumCongr_p2 fun a ha => ?_
      obtain ⟨-, -, ha2⟩ := hAann a ha
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0] at ha2
        rw [dist_self] at ha2
        linarith
      show lmfun (hl [0, a]) = lmfun (hl [u, a + u])
      rw [hlPairAdd_p2 ha0]
    unfold localAnnulusInequality at hLAI
    rw [key] at hLAI
    linarith

/-- HOL `GOTCJAH_concl` (pack_concl.hl:251-259): the fan solid-angle bound
for polyhedron facets. The HOL fan argument `(vec 0, fan_of_polyhedron s)`
is rendered by the two components of `fanOfPolyhedron s` feeding
`Kepler.Text.Fan.topologicalComponentYfan`. -/
theorem GOTCJAH_concl : ∀ (s : Set V3) (f : Set V3) (v : V3) (b : ℝ) (WF : Set V3)
    (h : ℝ) (k : ℕ), polyhedron s → Bornology.IsBounded s →
    (∃ r : ℝ, r > 0 ∧ Metric.ball 0 r ⊆ s) → FacetOf f s →
    f = {p : V3 | p ⬝ᵥ v = b} ∩ s →
    WF ∈ Kepler.Text.Fan.topologicalComponentYfan 0 (fanOfPolyhedron s).1
      (fanOfPolyhedron s).2 →
    f ∩ WF ≠ ∅ →
    rconeGt 0 v h ⊆ WF →
    k = Nat.card {u : V3 | u ∈ Set.extremePoints ℝ f} →
    2 * Real.pi - 2 * (k : ℝ) * Real.arcsin (h * Real.sin (Real.pi / k)) ≤
      sol 0 WF := by
  sorry

/-- HOL `TIWWFYQ_concl` (pack_concl.hl:263). -/
theorem TIWWFYQ_concl : ∀ (V : Set V3) (p : V3), Packing V → saturated V →
    ∃ v : V3, v ∈ V ∧ p ∈ voronoiClosed V v := by
  sorry

/-- HOL `VORONOI_BALL2_concl` (pack_concl.hl:266). -/
theorem VORONOI_BALL2_concl : ∀ (V : Set V3) (v : V3), Packing V → saturated V →
    v ∈ V → voronoiClosed V v ⊆ Metric.ball v 2 := by
  sorry

/-- HOL `VORONOI_INTER_BIS_LE_concl` (pack_concl.hl:268-269). -/
theorem VORONOI_INTER_BIS_LE_concl : ∀ (V : Set V3) (v : V3), Packing V → saturated V →
    v ∈ V →
    voronoiClosed V v =
      ⋂₀ ((fun u : V3 => bisLe v u) ''
        {u : V3 | u ∈ V ∧ u ∈ Metric.ball v 4 ∧ u ≠ v}) := by
  sorry

/-- HOL `VORONOI_POLYHEDRON_concl` (pack_concl.hl:271-272). -/
theorem VORONOI_POLYHEDRON_concl : ∀ (V : Set V3) (v : V3), Packing V → saturated V →
    v ∈ V → polyhedron (voronoiClosed V v) := by
  sorry

/-- HOL `RHWVGNP_concl` (pack_concl.hl:274): re-export of
`VORONOI_POLYHEDRON_concl`. -/
theorem RHWVGNP_concl : ∀ (V : Set V3) (v : V3), Packing V → saturated V →
    v ∈ V → polyhedron (voronoiClosed V v) :=
  VORONOI_POLYHEDRON_concl

/-- HOL `DRUQUFE_concl` (pack_concl.hl:276-277). -/
theorem DRUQUFE_concl : ∀ (V : Set V3) (v : V3), Packing V → saturated V →
    IsCompact (voronoiClosed V v) ∧ Convex ℝ (voronoiClosed V v) ∧
      MeasurableSet (voronoiClosed V v) := by
  sorry

/-- HOL `KHEJKCI_concl` (pack_concl.hl:287-288). (Hypothesis `vor_list` is
the reconstruction `vorList`; see the file header.) -/
theorem KHEJKCI_concl : ∀ (V : Set V3) (k : ℕ) (ul : List V3), saturated V →
    Packing V → vorList V k ul →
    FaceOf (voronoiList V ul) (voronoiClosed V (hdV ul)) := by
  sorry

/-- HOL `GRUTOTI1_concl` (pack_concl.hl:294-304): the dihedral angles of all
cells along a short edge sum to `2π`. -/
theorem GRUTOTI1_concl : ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3), saturated V →
    Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 → hl [u0, u1] < Real.sqrt 2 →
    e = {u0, u1} →
    setSum {X | mcellSet V X ∧ e ∈ edgeX V X} (fun t => dihX V t (u0, u1)) =
      2 * Real.pi := by
  sorry

/-- HOL `REUHADY_concl` (pack_concl.hl:306-321): the wedge contribution to
an edge sum equals the azimuth. (HL leaves `w1 w2` free — implicitly
generalized; bound explicitly here.) -/
theorem REUHADY_concl : ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3) (v1 v2 : V3)
    (e : Set V3) (w1 w2 : V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
    e = {u0, u1} → ¬(azim u0 u1 w1 w2 = 0) →
    hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 ∧ barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e ∧
    setOfList (truncateSimplex 1 vl2) = e ∧
    v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  sorry

/-- HOL `REUHADY_concl_version2` (pack_concl.hl:325-340): variant with the
wedge-intersection hypothesis instead of the azimuth non-degeneracy one. -/
theorem REUHADY_concl_version2 : ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
    (v1 v2 : V3) (e : Set V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
    e = {u0, u1} →
    wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
      affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} →
    hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 ∧ barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e ∧
    setOfList (truncateSimplex 1 vl2) = e ∧
    v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  sorry

end Kepler.Text
