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

/-! ## pack_concl.hl: conclusion statements (proofs `by sorry`) -/

/-- HOL `GLTVHUM_concl` (pack_concl.hl:17-19): the closed Voronoi cell of
`u0` is covered by the Rogers simplices rooted at `u0`. -/
theorem GLTVHUM_concl : ∀ (V : Set V3) (u0 p : V3), Packing V ∧ saturated V → u0 ∈ V →
    (p ∈ voronoiClosed V u0 ↔
      ∃ vl : List V3, barV V 3 vl ∧ p ∈ rogers V vl ∧ truncateSimplex 0 vl = [u0]) := by
  sorry

/-- HOL `DUUNHOR_concl` (pack_concl.hl:21-23): distinct Rogers simplices
meet in a coplanar set. -/
theorem DUUNHOR_concl : ∀ (V : Set V3) (ul vl : List V3), barV V 3 ul → barV V 3 vl →
    rogers V ul ≠ rogers V vl → Coplanar (rogers V ul ∩ rogers V vl) := by
  sorry

/-- HOL `QXSKIIT_concl` (pack_concl.hl:25-28): unique interpolation on the
affine hull. (HL states this over `real^N`; ported over `V3`.) -/
theorem QXSKIIT_concl : ∀ {A : Type} (vf : A → V3) (b : A → ℝ),
    (vf '' (Set.univ : Set A)).Finite → ¬affineDependent (vf '' (Set.univ : Set A)) →
    (∀ i j : A, vf i = vf j → b i = b j) →
    ∃! p : V3, p ∈ (affineSpan ℝ (vf '' (Set.univ : Set A)) : Set V3) ∧
      ∀ i j : A, p ⬝ᵥ (vf i - vf j) = b i - b j := by
  sorry

/-- HOL `OAPVION1_concl` (pack_concl.hl:35-36): the circumcenter lies on the
affine hull. -/
theorem OAPVION1_concl : ∀ S : Set V3, S ≠ ∅ → ¬affineDependent S →
    circumcenter S ∈ (affineSpan ℝ S : Set V3) := by
  sorry

/-- HOL `OAPVION2_concl` (pack_concl.hl:38-39): all points are at
circumradius distance from the circumcenter. -/
theorem OAPVION2_concl : ∀ S : Set V3, ¬affineDependent S →
    ∀ w ∈ S, radV S = dist (circumcenter S) w := by
  sorry

/-- HOL `OAPVION3_concl` (pack_concl.hl:41-42): characterization of the
circumcenter by equidistance on the affine hull. -/
theorem OAPVION3_concl : ∀ S : Set V3, ¬affineDependent S →
    ∀ p : V3, p ∈ (affineSpan ℝ S : Set V3) → (∃ c : ℝ, ∀ w ∈ S, dist p w = c) →
      p = circumcenter S := by
  sorry

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

/-- HOL `RVFXZBU3_concl` (pack_concl.hl:149-150). -/
theorem RVFXZBU3_concl : ∀ (V : Set V3) (ul : List V3) (i : ℕ) (p : Equiv.Perm ℕ),
    saturated V → Packing V → barV V 3 ul → permutes p (Set.Icc 0 (i - 1)) →
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

/-- HOL `RDWKARC_concl` (pack_concl.hl:247-249, modified Dec 31 2012). -/
theorem RDWKARC_concl : ¬keplerConjecture →
    (∀ V : Set V3, Packing V → saturated V → cellClusterInequality V) →
    TSKAJXY_statement →
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬localAnnulusInequality V := by
  sorry

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
