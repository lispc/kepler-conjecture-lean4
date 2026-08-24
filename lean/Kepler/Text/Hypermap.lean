/-
Port of the HOL Light Flyspeck hypermap theory (core definition layer).

Source: `reference/flyspeck/text_formalization/hypermap/hypermap.hl`
(Flyspeck book formalization, Tran Nam Trung, 2010).

Coverage (block 1, core definitions):
- `hypermap.hl` lines 25–205, all definitions: `res`, `orbit_map`, the
  `hypermap` type with accessors (`dart`/`edge_map`/`node_map`/`face_map`),
  `edge`/`node`/`face`, `go_one_step`/`is_path`/`is_in_component`/
  `comb_component`, `set_part_components`/`set_of_components`,
  `set_of_orbits`/`number_of_orbits`, `edge_set`/`node_set`/`face_set`,
  `number_of_edges`/`number_of_nodes`/`number_of_faces`/
  `number_of_components`, and the degeneracy predicates
  (`plain_hypermap`, `planar_hypermap`, `simple_hypermap`,
  `dart_(non)degenerate`, `is_(edge|node|face)_nondegenerate`).
- The basic permutation/orbit lemmas of lines 222–306: `iterate_orbit`,
  `orbit_subset`, `in_orbit_lemma`, `lemma_in_orbit`, `orbit_one_point`,
  `lemma_orbit_finite`, plus the inverse-equation corollaries of
  `edge_map o node_map o face_map = I` (cf. lines 211–220).

Coverage (block 2, orbit iteration / components / orbit counting):
- Orbit iteration and equivalence: `orbit_cyclic` (308), `power_permutation`
  (321), `inverse_power_function` (366), `edge/node/face_map_inverse_
  representation` (374–386), `node/face_map_injective` (388–395),
  `lemma_dart_invariant` and variants (412–431), `finite_order` (753),
  `inverse_element_lemma` (770), `inverse_relation` (805),
  `power_power_relation` (812), `orbit_sym` (835), `orbit_trans` (849),
  `partition_orbit` (861), `card_orbit_le` (876),
  `lemma_orbit_convolution_map` (1203), `lemma_nondegenerate_convolution`
  (1213), plus `lemma_orbit_identity` (2123, pulled forward as
  `orbitMap_eq_of_mem`).
- Cyclic and inverse map relations: `cyclic_maps` (887, as
  `perm_mul_eq_one_rotate`), `hypermap_cyclic` (913),
  `inverse_hypermap_maps` (923), `inverse2_hypermap_maps` (937).
- Connected hypermaps: `connected_hypermap` (1000).
- Components: `lemma_subpath` (1258, as `isPath_mono` in block 1),
  `lemma_path_subset` (1263), `lemma_component_subset` (1272),
  `lemma_edge/node/face_subset` (1277–1284, as `*_subset_darts` in block 1),
  `lemma_component_reflect` (1286, as `mem_combComponent_self`),
  `lemma_def_path` (1292), `edge/node/face_path` (1300–1307) with
  `lemma_edge/node/face_path` (1309–1325), `glue` (637, as `gluePaths`)
  with `first/second_glue_evaluation` (642–651), `lemma_glue_paths` (1329),
  `concatenate_two_paths`/`concatenate_paths` (1351–1363),
  `lemma_component_trans` (1365, as `isInComponent_trans` in block 1),
  `lemma_reverse_path` (1372), `lemma_component_symmetry` (1417),
  `partition_components` (1423), `lemma_partition_by_components` (1439);
  plus `isInComponent_equivalence` (the equivalence-relation closure).
- Orbit counting: `finite_orbits_lemma` (1053, as `setOfOrbits_finite` in
  block 1), `lemma_partition` (1060), `card_partition_formula` (1146),
  `lemma_card_lower_bound` (1167), `lemma_card_eq` (1185), and the
  Euler-type bound `lemmaTGJISOK` (1228, as `darts_card_le`).

Explicitly skipped (with reason; nothing is silently omitted):
- 397–407 `label_*_TAC`: HOL tactic plumbing, no Lean counterpart needed.
- 435–466 `IMAGE_SEG`/`FINITE_SERIES`/`CARD_FINITE_SERIES_(LE|EQ)`/`LEMMA_INJ`:
  subsumed by `Set.ncard_image_le` over `Finset.range` (used in
  `card_orbit_le`); the injective-cardinality variant has no downstream
  consumer in the ported range.
- 468–536 arithmetic scratch lemmas: subsumed by `omega`/Mathlib.
- 540–634 `is_inj_list`/`support_of_sequence` machinery: only consumed by
  the join/walkup counting theory later in the file (out of scope here);
  path concatenation is proved directly via `gluePaths`.
- 690–732 `join`/`lemma_join_inj_lists`: same reason (disjoint-join version
  of glueing, unused in the ported range).
- 736–749 `inj_iterate_lemma`: `finite_order` is proved via the induced
  permutation on the subtype `↥s` and `pow_card_eq_one` instead.
- 948–996 `lemmaZHQCZLX`: standalone side fact (simple+plain hypermaps have
  no node-fixed darts); not needed by the counting/component chain.
- 1003–1042 singleton/pair cardinality helpers: subsumed by
  `Set.ncard_singleton`/`Set.ncard_pair`.
- 1067–1144 `lemma_card_of_disjoint_covering`: replaced by Mathlib's
  `Set.Finite.ncard_biUnion`.

Coverage (block 3, contour paths and walkup basics):
- Contour paths (1453–1628, complete): `one_step_contour` (1455),
  `is_contour` (1457), `lemma_subcontour` (1460, as `isContour_mono`),
  `lemma_def_contour` (1468, as `isContour_iff`), `lemma_glue_contours`
  (1473, as `isContour_gluePaths`), `concatenate_contours` (1495),
  `node_contour` (1508), `face_contour` (1512), `lemma_node_contour`
  (1514), `lemma_face_contour` (1522), `existence_contour` (1530, proved
  directly by induction + `PermutesOn.exists_pow_eq_inv`/
  `exists_pow_apply_eq` instead of HOL's detour),
  `is_inj_contour` (1597), `lemma_sub_inj_contour` (1601, as
  `isInjContour_mono`), `lemma_def_inj_contour` (1608, as
  `isInjContour_iff`).
- Walkup basics (1632–1978): `isolated_dart`/`is_(edge|node|face)_degenerate`
  (1632–1641), `degenerate_lemma` (1644, as `dartDegenerate_iff`),
  `lemma_category_darts` (1670), `shift`/`shift_lemma`/
  `double_shift_lemma` (1706–1717), `edge_walkup`/`node_walkup`/
  `face_walkup`/double walkups (1721–1731), `walkup_permutes` (1733, as
  `PermutesOn.swap_mul_erase`), `PERMUTES_COMPOSITION` (1748, as
  `PermutesOn.mul`), `lemma_edge_walkup` (1751, `rfl` under the structure
  encoding), `node_map_walkup` (1781), `face_map_walkup` (1798),
  `lemma_(edge|node|face)_degenerate` (1815–1852),
  `fixed_point_lemma` (1854), `non_fixed_point_lemma` (1864),
  `lemma_inverse_maps_at_nondegenerate_dart` (1868),
  `aux_permutes_conversion` (1872, as `Perm_inv_apply_inv_apply_iff`),
  `edge_map_walkup` (1880, as `edgeMap_walkup`; the proof goes through the
  `aux_permutes_conversion` normal form instead of HOL's label-tactic chain).

Explicitly skipped in this range:
- 1681–1696 `lemma_pair_*`/`lemma_hypermap_eq`: artifacts of HOL's
  4-tuple encoding of hypermaps; Lean's `structure Hypermap` has
  `ext`/proof irrelevance built in.
- 1698 `lemma_hypermap_rep`: under the structure encoding the projections
  of `⟨D, e, n, f, _⟩` hold by `rfl` (cf. `lemma_edge_walkup`).

Coverage (block 4, fine orbit structure / planar index / walkup orbits):
- Fine orbit structure (1982–2097): `power_sequence` (1982, as
  `powerSeq`), `inj_orbit` (1984, defined directly without the
  `is_inj_list` detour), `lemma_def_inj_orbit` (1995, as `injOrbit_iff`),
  `lemma_inj_orbit` (2000, as `injOrbit_iff_pairwise`),
  `elim_power_function` (820, as `Perm.pow_apply_eq_pow_apply_cancel`),
  `inj_orbit_step` (2003, as `PermutesOn.injOrbit_step`; the `permutes`
  hypothesis is kept for fidelity although the `Equiv.Perm` proof only
  needs injectivity), `lemma_subset_orbit` (2022), `lemma_segment_orbit`
  (2027, as `PermutesOn.injOrbit_of_lt_ncard`), `lemma_cycle_orbit` (2039,
  as `PermutesOn.pow_ncard_orbitMap_apply_self`), `lemma_index_on_orbit`
  (2064), `lemma_congruence_on_orbit` (2076).
- Merge/split classification (2103–2113, definitions only).
- Orbit identities (2115–2164): `INVERSE_EVALUATION` (2115),
  `lemma_orbit_identity` (2123, already ported as `orbitMap_eq_of_mem`),
  `lemma_edge/node/face_identity` (2138–2144), `lemma_orbit_power` (2152),
  `lemma_inverse_in_orbit` (2159).
- Planarity (2168–2260): `planar_index` (2170, over `ℤ` instead of HOL's
  `&`/ℝ — equivalent for the counting arguments and omega-friendly),
  `lemma_planar_hypermap` (2175), `lemma_null_hypermap_planar_index`
  (2179), `lemma_shift_component_invariant` (2190),
  `lemma_planar_invariant_shift` (2251), `in_orbit_map1` (2258).
- `lemma_orbit_eq` (2263), `lemma_not_in_orbit_powers` (2275).
- Walkup orbit equalities (2286–2507): `lemma_walkup_nodes` (2286) and
  `lemma_walkup_faces` (2397), both as instances of a single generic
  lemma `walkup_orbits_delete` (the two HOL proofs are verbatim copies
  with `node_map`/`face_map` exchanged).

Explicitly skipped in this range:
- 1988 `lemma_inj_orbit_via_list`: goes through the `is_inj_list`
  machinery skipped in block 2; `injOrbit` is given equivalent
  characterizations (`injOrbit_iff`, `injOrbit_iff_pairwise`) instead.
- 2147 `lemma_in_disjoint`: set-theoretic triviality (Mathlib).
- 2508–2706 `lemma_walkup_first/second_edge_eq`, `lemma_walkup_edges`:
  left for the next block (walkup edge-set equalities).
- 2708 onwards (`in_set_of_orbits`, representation lemmas, component
  walkups, planar-index computations): left for the next block.

Coverage (block 5, walkup edge/component equalities):
- Walkup edge equalities (2508–2706): `lemma_walkup_first_edge_eq` (2508),
  `lemma_walkup_second_edge_eq` (2559), `lemma_walkup_edges` (2612, as
  `edgeSet_walkup`). The two HOL proofs share the same
  "powerwise-equal outside the seam" induction; the seam avoidance comes
  from `edgeMap_walkup`'s fourth component.
- Orbit membership (2708–2741): `in_set_of_orbits` (2708, as
  `PermutesOn.mem_iff_orbitMap_mem_setOfOrbits`),
  `lemma_in_hypermap_orbits` (2721, as `mem_darts_iff`),
  `lemma_in_(edge|node|face)_set` (2725–2727),
  `lemma_(edge|node|face)_representation` (2729–2737).
- Component walkups (3027–3508): `lemma_powers_in_component` (3029),
  `lemma_inverses_in_component` (3044), `lemma_(node|face)_subset_
  component` (3060/3068, plus the symmetric edge version),
  `lemma_component_identity` (3076, as `combComponent_eq_of_mem`),
  `lemma_walkup_first_component_eq` (3089),
  `lemma_walkup_second_component_eq` (3272), `lemma_walkup_components`
  (3436, as `setOfComponents_walkup`). The HOL mutual-induction path
  conversions are factored through `goOneStep_edgeWalkup_iff`/
  `isPath_edgeWalkup_iff` (steps coincide away from the seam points)
  plus `isInComponent_trans_step`.

Explicitly skipped in this range:
- 2741 `lemma_in_subset`: set-theoretic triviality (Mathlib).
- 2744–3025 (`lemma_complement_two_edges`, walkup-in-dart facts,
  `lemma_walkup_support_edges`, `lemma_edge_split`/`lemma_edge_merge`):
  edge split/merge characterizations, left for the next block together
  with the planar-index counting chain.
- 3509 onwards (degenerate walkups, component counts,
  `lemma_planar_index_on_*`, `lemmaFOAGLPA`): the planar-index counting
  chain proper, left for the next block.

Coverage (block 6, planar-index counting chain, complete):
- Edge split/merge infrastructure (2744–3025): `lemma_complement_two_edges`
  (2744), `lemma_(edge|node|face)_map_walkup_in_dart` (2791–2817),
  `lemma_walkup_support_edges` (2819), `lemma_in_edge`/`lemma_in_edge2`
  (2850–2853), `lemma_edge_cycle` (2855), `lemma_edge_split` (2860),
  `lemma_edge_merge` (2966). The two HOL proofs' shared power-chain
  (`(e'^i)(e x) = (e^i)(e x)` outside the seam) is factored through
  `injOrbit` avoidance conditions.
- Degenerate walkups (3509–3880): `edge/node/face_degenerate_walkup_*`
  map evaluations (3511–3649), `edge_degenerate_walkup_(first|second|
  third)_eq` (3654–3804), `lemma_shift_cycle` (3806, as `shift_cycle`),
  `lemma_eq_iff_shift_eq` (3811), `lemma_degenerate_walkup_(first|
  second)_eq` (3818–3878). `lemma_hypermap_eq` (1689) is realized as
  `Hypermap.ext'`; map equalities use the `comp_eq_one` cancellation
  `nodeMap_eq_of_edgeMap_faceMap_eq`.
- Planar-index counting (3883–4790, complete): `component_at_isolated_
  dart` (3883), CARD helpers as `ncard_diff_singleton_mem`/
  `ncard_diff_pair_mem` (3913–3935), `NODE/FACE_NOT_EMPTY` (3951–3968),
  `FINITE_HYPERMAP_ORBITS`/`FINITE_HYPERMAP_COMPONENTS` (3970–3989,
  already in block 1), `WALKUP_EXCEPTION_COMPONENT` (3989),
  `lemma_in_components` (4003), `lemma_different_(edges|nodes|faces)`
  (4019–4047), `lemma_planar_index_on_walkup_at_(isolated|edge_degenerate|
  degenerate)_dart` (4053–4426), `lemma_card_walkup_dart` (4432),
  `lemma_splitting_case_count_edges` (4440), `lemma_merge_case_count_edges`
  (4491), `lemma_walkup_count_(nodes|faces)` (4540–4584),
  `lemma_walkup_count_(splitting|not_splitting)_components` (4589–4636),
  `is_splitting_component` (4639, as `IsSplittingComponent`),
  `lemma_planar_index_on_nondegenerate` (4641), `lemma_desc_planar_index`
  (4705, as `planarIndex_le_edgeWalkup`), `lemmaBISHKQW` (4721, as
  `planarIndex_le_walkups`), **`lemmaFOAGLPA`** (4741, as
  `planarIndex_le_zero`, by induction on the dart count), and
  **`lemmaSGCOSXK`** (4771, as `planar_walkup`).

Explicitly skipped in this range:
- 4017 `lemma_card_eq_reflect`: triviality.
- 4790 onwards (double walkups, convolutions, `iso`, ...): next block.

Coverage (block 7, convolution / Moebius contour basics):
- Convolution (4793–4935, complete): `convolution_rep` (4793, as
  `mul_self_eq_one_iff_eq_inv`), `convolution_inv` (4801),
  `convolution_belong` (4816, as `PermutesOn.mul_self_eq_one_iff`),
  `edge_convolution` (4834), `edge_map_convolution` (4843),
  `lemma_convolution_evaluation` (4850), `lemma_orbit_of_size_2` (4869),
  `NODE_OF_SIZE_2` (4895), `power_permutation_outside_domain` (4905),
  `lemma_(node|face)_exception` (4915–4925), `lemma_simple_hypermap`
  (4927, as `Simple.apply`).
- Moebius contour basics (4939–5058): `is_Moebius_contour` (4941),
  `lemma_contour_in_dart` (4943), `lemma_darts_in_contour` (4964, with
  the point set written as the image of `Finset.range`), `lemma_first_
  dart_on_inj_contour` (4975), `lemma_darts_on_Moebius_contour` (5006),
  `lemma_Moebius_contour_points_subset_darts` (5029),
  `lemma_darts_is_Moebius_contour` (5045),
  `lemma_point_(not_)in_support_of_sequence` (5053–5058).
- Path shifting/joining (5174–5276): `shift_path` (5174),
  `lemma_shift_contour` (5178), `lemma_shift_inj_contour` (5191),
  `join` (690, as `joinPaths`) with its evaluations, `lemma_join_contours`
  (5204), `lemma_join_inj_contours` (5237), `is_glueing` (653, as
  `IsGlueing`), `lemma_glue_inj_contours` (5249),
  `concatenate_two_contours` (5257),
  `concatenate_two_disjoint_contours` (5266). The join/glue injective
  lemmas are re-proved directly via `isInjContour_iff`'s pairwise
  characterization, bypassing the skipped `is_inj_list` machinery.
- `lemma_one_step_contour` (5353, as `oneStepContour_iff`),
  `lemma_only_one_orbit` (5360), `lemma_only_one_component` (5383).

Explicitly skipped in this range:
- 5061–5173 `lemma_eliminate_dart_ouside_Moebius_contour`: walkup
  preservation of Moebius contours (~110 lines); left for the Jordan
  chain block.
- 5279–5352 `lemmaQZTPGJV` (contour-to-injective-contour extraction):
  needed only by the Jordan curve theorem; left for that block.
- 5406–5626 `lemma_minimum_Moebius_hypermap` (order-3 Moebius
  hypermap): large standalone construction; left for the Jordan chain.
- 5627 onwards (`dart_face_walkup`, node/face walkup map lemmas,
  `lemmaLIPYTUI`): the combinatorial Jordan curve theorem chain; next
  block(s).
- 9614+ `iso` (hypermap isomorphism): far ahead in the file; will be
  reached in file order.

Coverage (block 8, walkup contour preservation and elimination):
- `lemma_eliminate_dart_ouside_Moebius_contour` (5061, as
  `isMoebiusContour_edgeWalkup_of_not_mem_support`; the HOL label-tactic
  case analysis is factored through three key lemmas converting
  node/face map relations across the walkup seam).
- `lemmaQZTPGJV` (5279, as `exists_injContour_of_isContour`: every
  contour refines to an injective contour with the same endpoints).
- Face/node walkup facts (5627–5689): `dart_(face|node)_walkup`
  (5629/5662, `rfl` under the structure encoding),
  `lemma_card_(face|node)_walkup_dart` (5636/5669),
  `face_map_face_walkup` (5641), `node_map_face_walkup` (5652),
  `node_map_node_walkup` (5675), `face_map_node_walkup` (5683) — these
  are literally `edgeMap_walkup`/`nodeMap_walkup`/`faceMap_walkup`
  instantiated at `shift H`/`shift (shift H)`, one line each.
- `lemma_face_walkup_second_segment_contour` (5691, as
  `isInjContour_faceWalkup_shift`), `lemma_face_walkup_eliminate_dart_
  on_Moebius_contour` (5774, as `isInjContour_faceWalkup_eliminate`),
  `lemma_node_walkup_second_segment_contour` (5888, as
  `isInjContour_nodeWalkup_shift`), `lemma_node_walkup_eliminate_dart_
  on_Moebius_contour` (5969, as `isInjContour_nodeWalkup_eliminate`).
  Seam avoidance is driven by the new `ne_of_pairwise` helper on the
  injective path.

Explicitly skipped in this range:
- 5406–5626 `lemma_minimum_Moebius_hypermap`: still open (belongs with
  the Jordan applications).
- 6080–6696 `lemmaLIPYTUI` (the combinatorial Jordan curve theorem):
  the ~615-line multi-case induction; all its prerequisites up to this
  line are now ported, the theorem itself is the next block's target.

Type correspondences (HOL Light ↦ Lean 4):
- `(A)hypermap` (a 4-tuple carrying `FINITE`/`permutes` side conditions,
  `hypermap.hl`:83–93) ↦ `structure Hypermap` with a `Finset` of darts and
  `Equiv.Perm` maps.  Bijectivity is built into `Equiv.Perm`, so HOL's
  `f permutes s` (identity outside `s` + unique preimage) reduces to
  `PermutesOn f s`, the pointwise-identity-outside-`s` condition.
- composition `f o g` and identity `I` on `A → A` ↦ multiplication `f * g`
  and `1` in `Equiv.Perm α` (`Equiv.Perm.mul_apply : (f * g) x = f (g x)`);
  hence `edge_map H o node_map H o face_map H = I` ↦
  `edgeMap * nodeMap * faceMap = 1` (a global equality of permutations,
  which implies the dartwise version used in later Flyspeck files).
- `f POWER n` (`hypermap.hl`:36) ↦ `(f ^ n : Equiv.Perm α)`;
  `addition_exponents`/`multiplication_exponents` are then `pow_add`/`pow_mul`.
- `orbit_map f x` (a HOL set of iterates) ↦ `orbitMap f x : Set α`;
  finiteness is recovered from `PermutesOn` (`orbitMap_finite`).
- `CARD` of a set of sets ↦ `Set.ncard` (all sets involved are finite here).
- `dart H` (the dart *set*) ↦ `H.darts`.

Design choices (deviating from the task sketch where noted):
- `Hypermap` carries `[DecidableEq α]` as suggested; the instance is not
  used by the fields themselves but by `res` and by later computational
  lemmas (decidable `Finset` membership).
- Orbits and component sets are `Set`-valued (not `Finset`-valued) to keep
  the definitions noncomputable-free and order-agnostic; finiteness is
  provided as separate lemmas (`orbitMap_finite`, `edgeSet_finite`, ...).
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card.Arithmetic

namespace Kepler.Text

section Res

variable {α : Type*} [DecidableEq α]

/-- `hypermap.hl`:29 `res`. 函数在集合 `s` 外限制为恒等。 -/
def res (f : α → α) (s : Finset α) (x : α) : α := if x ∈ s then f x else x

theorem res_apply_of_mem {f : α → α} {s : Finset α} {x : α} (h : x ∈ s) :
    res f s x = f x := if_pos h

theorem res_apply_of_not_mem {f : α → α} {s : Finset α} {x : α} (h : x ∉ s) :
    res f s x = x := if_neg h

end Res

section Permutations

variable {α : Type*}

/-- HOL Light 中 `f permutes s` 的 `Equiv.Perm` 版本：置换在 `s` 外逐点为恒等
（双射性已由 `Equiv.Perm` 自带，故无需 HOL 的 "∃! 原像" 部分）。 -/
def PermutesOn (f : Equiv.Perm α) (s : Finset α) : Prop := ∀ x ∉ s, f x = x

namespace PermutesOn

variable {f : Equiv.Perm α} {s : Finset α} {x : α}

theorem apply_mem (hf : PermutesOn f s) (hx : x ∈ s) : f x ∈ s := by
  by_contra h
  have h1 : f (f x) = f x := hf (f x) h
  have h2 : f x = x := f.injective h1
  exact h (h2.symm ▸ hx)

/-- `f` 在 `s` 外为恒等，则 `f.symm` 亦然。 -/
theorem symm (hf : PermutesOn f s) : PermutesOn f.symm s := by
  intro x hx
  calc f.symm x = f.symm (f x) := by rw [hf x hx]
    _ = x := f.symm_apply_apply x

theorem symm_apply_mem (hf : PermutesOn f s) (hx : x ∈ s) : f.symm x ∈ s :=
  hf.symm.apply_mem hx

/-- `hypermap.hl`:222 `iterate_orbit`（`permutes` 版本）。 -/
theorem pow_apply_mem (hf : PermutesOn f s) (n : ℕ) (hx : x ∈ s) : (f ^ n) x ∈ s := by
  induction n with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hf.apply_mem ih

end PermutesOn

/-- `hypermap.hl`:49 `orbit_map`。置换 `f` 在 `x` 处（非负幂下）的轨道。 -/
def orbitMap (f : Equiv.Perm α) (x : α) : Set α := {y | ∃ n : ℕ, (f ^ n) x = y}

variable {f : Equiv.Perm α} {s : Finset α} {x : α}

/-- `hypermap.hl`:274/279 `in_orbit_lemma`/`lemma_in_orbit` 的特例（`n = 0`）。 -/
theorem mem_orbitMap_self (f : Equiv.Perm α) (x : α) : x ∈ orbitMap f x :=
  ⟨0, by simp⟩

/-- `hypermap.hl`:279 `lemma_in_orbit`。 -/
theorem pow_apply_mem_orbitMap (f : Equiv.Perm α) (n : ℕ) (x : α) :
    (f ^ n) x ∈ orbitMap f x := ⟨n, rfl⟩

/-- `hypermap.hl`:228 `orbit_subset`。 -/
theorem orbitMap_subset_of_permutesOn (hf : PermutesOn f s) (hx : x ∈ s) :
    orbitMap f x ⊆ ↑s := by
  rintro y ⟨n, rfl⟩
  exact hf.pow_apply_mem n hx

/-- `hypermap.hl`:284 `orbit_one_point` 的 `→` 方向。 -/
theorem orbitMap_eq_singleton (h : f x = x) : orbitMap f x = {x} := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    have key : ∀ n : ℕ, (f ^ n) x = x := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h]
    rw [Set.mem_singleton_iff]
    exact key n
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mem_orbitMap_self _ _

/-- `hypermap.hl`:284 `orbit_one_point`。 -/
theorem orbitMap_singleton_iff (f : Equiv.Perm α) (x : α) :
    orbitMap f x = {x} ↔ f x = x := by
  constructor
  · intro h
    have h1 : (f ^ 1) x ∈ orbitMap f x := pow_apply_mem_orbitMap f 1 x
    rw [h, Set.mem_singleton_iff] at h1
    simpa using h1
  · exact orbitMap_eq_singleton

/-- `hypermap.hl`:297 `lemma_orbit_finite`。 -/
theorem orbitMap_finite (hf : PermutesOn f s) (x : α) : (orbitMap f x).Finite := by
  by_cases hx : x ∈ s
  · exact s.finite_toSet.subset (orbitMap_subset_of_permutesOn hf hx)
  · rw [orbitMap_eq_singleton (hf x hx)]
    exact Set.finite_singleton x

end Permutations

/-- `hypermap.hl`:92 `hypermap` 类型（由 `exist_hypermap`（83 行）保证非空的四元组）。
dart 集合用 `Finset`（有限性内置，对应 `FINITE (dart H)`）；三个映射用
`Equiv.Perm`（双射性内置，`permutes` 只剩"集合外恒等"一条）。 -/
structure Hypermap (α : Type*) [DecidableEq α] where
  /-- dart 集合（`hypermap.hl`:95 `dart`）。 -/
  darts : Finset α
  /-- `hypermap.hl`:97 `edge_map`。 -/
  edgeMap : Equiv.Perm α
  /-- `hypermap.hl`:99 `node_map`。 -/
  nodeMap : Equiv.Perm α
  /-- `hypermap.hl`:101 `face_map`。 -/
  faceMap : Equiv.Perm α
  /-- `hypermap_lemma` 合取项：`edge_map H permutes dart H`。 -/
  edgeMap_permutes : PermutesOn edgeMap darts
  /-- `hypermap_lemma` 合取项：`node_map H permutes dart H`。 -/
  nodeMap_permutes : PermutesOn nodeMap darts
  /-- `hypermap_lemma` 合取项：`face_map H permutes dart H`。 -/
  faceMap_permutes : PermutesOn faceMap darts
  /-- `hypermap_lemma` 合取项：`edge_map H o node_map H o face_map H = I`。 -/
  comp_eq_one : edgeMap * nodeMap * faceMap = 1

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `hypermap.hl`:103 `hypermap_lemma`。
（HOL 版另有 `FINITE (dart H)` 一项，此处由 `Finset` 内置。） -/
theorem hypermap_lemma (H : Hypermap α) :
    PermutesOn H.edgeMap H.darts ∧ PermutesOn H.nodeMap H.darts ∧
      PermutesOn H.faceMap H.darts ∧ H.edgeMap * H.nodeMap * H.faceMap = 1 :=
  ⟨H.edgeMap_permutes, H.nodeMap_permutes, H.faceMap_permutes, H.comp_eq_one⟩

/-- `hypermap.hl`:111 `edge_map_and_darts`。 -/
theorem edgeMap_and_darts (H : Hypermap α) :
    (↑H.darts : Set α).Finite ∧ PermutesOn H.edgeMap H.darts :=
  ⟨H.darts.finite_toSet, H.edgeMap_permutes⟩

/-- `hypermap.hl`:114 `node_map_and_darts`。 -/
theorem nodeMap_and_darts (H : Hypermap α) :
    (↑H.darts : Set α).Finite ∧ PermutesOn H.nodeMap H.darts :=
  ⟨H.darts.finite_toSet, H.nodeMap_permutes⟩

/-- `hypermap.hl`:117 `face_map_and_darts`。 -/
theorem faceMap_and_darts (H : Hypermap α) :
    (↑H.darts : Set α).Finite ∧ PermutesOn H.faceMap H.darts :=
  ⟨H.darts.finite_toSet, H.faceMap_permutes⟩

/-- `edgeMap` 把 dart 映为 dart（`iterate_orbit` 的一步版本）。 -/
theorem edgeMap_apply_mem (H : Hypermap α) (hx : x ∈ H.darts) : H.edgeMap x ∈ H.darts :=
  H.edgeMap_permutes.apply_mem hx

theorem nodeMap_apply_mem (H : Hypermap α) (hx : x ∈ H.darts) : H.nodeMap x ∈ H.darts :=
  H.nodeMap_permutes.apply_mem hx

theorem faceMap_apply_mem (H : Hypermap α) (hx : x ∈ H.darts) : H.faceMap x ∈ H.darts :=
  H.faceMap_permutes.apply_mem hx

theorem edgeMap_symm_apply_mem (H : Hypermap α) (hx : x ∈ H.darts) :
    H.edgeMap.symm x ∈ H.darts := H.edgeMap_permutes.symm_apply_mem hx

theorem nodeMap_symm_apply_mem (H : Hypermap α) (hx : x ∈ H.darts) :
    H.nodeMap.symm x ∈ H.darts := H.nodeMap_permutes.symm_apply_mem hx

theorem faceMap_symm_apply_mem (H : Hypermap α) (hx : x ∈ H.darts) :
    H.faceMap.symm x ∈ H.darts := H.faceMap_permutes.symm_apply_mem hx

/-- 由 `edgeMap * nodeMap * faceMap = 1` 得到的逆元变形
（对应 `hypermap.hl`:211–220 `LEFT_INVERSE_EQUATION`/`RIGHT_INVERSE_EQUATION` 的应用）。 -/
theorem faceMap_eq_inv (H : Hypermap α) : H.faceMap = (H.edgeMap * H.nodeMap)⁻¹ :=
  eq_inv_of_mul_eq_one_right H.comp_eq_one

theorem edgeMap_mul_nodeMap (H : Hypermap α) : H.edgeMap * H.nodeMap = H.faceMap⁻¹ :=
  eq_inv_of_mul_eq_one_left H.comp_eq_one

theorem nodeMap_mul_faceMap (H : Hypermap α) : H.nodeMap * H.faceMap = H.edgeMap⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← mul_assoc]; exact H.comp_eq_one)

/-- `hypermap.hl`:122 `edge`。 -/
def edge (H : Hypermap α) (x : α) : Set α := orbitMap H.edgeMap x

/-- `hypermap.hl`:124 `node`。 -/
def node (H : Hypermap α) (x : α) : Set α := orbitMap H.nodeMap x

/-- `hypermap.hl`:126 `face`。 -/
def face (H : Hypermap α) (x : α) : Set α := orbitMap H.faceMap x

theorem edge_subset_darts (H : Hypermap α) (hx : x ∈ H.darts) : H.edge x ⊆ ↑H.darts :=
  orbitMap_subset_of_permutesOn H.edgeMap_permutes hx

theorem node_subset_darts (H : Hypermap α) (hx : x ∈ H.darts) : H.node x ⊆ ↑H.darts :=
  orbitMap_subset_of_permutesOn H.nodeMap_permutes hx

theorem face_subset_darts (H : Hypermap α) (hx : x ∈ H.darts) : H.face x ⊆ ↑H.darts :=
  orbitMap_subset_of_permutesOn H.faceMap_permutes hx

theorem mem_edge_self (H : Hypermap α) (x : α) : x ∈ H.edge x := mem_orbitMap_self _ _

theorem mem_node_self (H : Hypermap α) (x : α) : x ∈ H.node x := mem_orbitMap_self _ _

theorem mem_face_self (H : Hypermap α) (x : α) : x ∈ H.face x := mem_orbitMap_self _ _

theorem edge_finite (H : Hypermap α) (x : α) : (H.edge x).Finite :=
  orbitMap_finite H.edgeMap_permutes x

theorem node_finite (H : Hypermap α) (x : α) : (H.node x).Finite :=
  orbitMap_finite H.nodeMap_permutes x

theorem face_finite (H : Hypermap α) (x : α) : (H.face x).Finite :=
  orbitMap_finite H.faceMap_permutes x

/-- `hypermap.hl`:131 `go_one_step`。 -/
def goOneStep (H : Hypermap α) (x y : α) : Prop :=
  y = H.edgeMap x ∨ y = H.nodeMap x ∨ y = H.faceMap x

/-- `hypermap.hl`:135 `is_path`。 -/
def isPath (H : Hypermap α) (p : ℕ → α) : ℕ → Prop
  | 0 => True
  | n + 1 => isPath H p n ∧ goOneStep H (p n) (p (n + 1))

theorem isPath_succ (H : Hypermap α) (p : ℕ → α) (n : ℕ) :
    H.isPath p (n + 1) ↔ H.isPath p n ∧ H.goOneStep (p n) (p (n + 1)) := Iff.rfl

/-- 路径性质只依赖于前 `n` 个点的取值。 -/
theorem isPath_congr (H : Hypermap α) {p p' : ℕ → α} {n : ℕ}
    (h : ∀ k ≤ n, p k = p' k) : H.isPath p n ↔ H.isPath p' n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [H.isPath_succ, H.isPath_succ, ih (fun i hi => h i (Nat.le_succ_of_le hi)),
      h k k.le_succ, h (k + 1) le_rfl]

/-- `is_path` 对长度单调：长路径截短后仍是路径。 -/
theorem isPath_mono (H : Hypermap α) {p : ℕ → α} {n m : ℕ}
    (h : H.isPath p n) (hmn : m ≤ n) : H.isPath p m := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hmn
    exact h
  | succ k ih =>
    rw [H.isPath_succ] at h
    rcases (by omega : m ≤ k ∨ m = k + 1) with hle | heq
    · exact ih h.1 hle
    · subst heq
      exact (H.isPath_succ p k).mpr h

/-- 长路径的第 `j` 步是合法步（`j + 1 ≤ n`）。 -/
theorem goOneStep_of_isPath (H : Hypermap α) {p : ℕ → α} {n j : ℕ}
    (h : H.isPath p n) (hj : j + 1 ≤ n) : H.goOneStep (p j) (p (j + 1)) :=
  ((H.isPath_succ p j).mp (H.isPath_mono h hj)).2

/-- `hypermap.hl`:140 `is_in_component`。 -/
def isInComponent (H : Hypermap α) (x y : α) : Prop :=
  ∃ p : ℕ → α, ∃ n : ℕ, p 0 = x ∧ p n = y ∧ H.isPath p n

/-- `hypermap.hl`:142 `comb_component`。 -/
def combComponent (H : Hypermap α) (x : α) : Set α := {y | H.isInComponent x y}

theorem mem_combComponent (H : Hypermap α) (x y : α) :
    y ∈ H.combComponent x ↔ H.isInComponent x y := Iff.rfl

theorem isInComponent_refl (H : Hypermap α) (x : α) : H.isInComponent x x :=
  ⟨fun _ => x, 0, rfl, rfl, True.intro⟩

theorem mem_combComponent_self (H : Hypermap α) (x : α) : x ∈ H.combComponent x :=
  H.isInComponent_refl x

/-- `is_in_component` 的传递性：两条路径首尾相接。 -/
theorem isInComponent_trans (H : Hypermap α)
    (hxy : H.isInComponent x y) (hyz : H.isInComponent y z) : H.isInComponent x z := by
  obtain ⟨p, n, hp0, hpn, hp⟩ := hxy
  obtain ⟨q, m, hq0, hqm, hq⟩ := hyz
  -- 拼接路径：`n` 之前走 `p`，之后走 `q`。
  set r := fun i => if i ≤ n then p i else q (i - n) with hr
  refine ⟨r, n + m, ?_, ?_, ?_⟩
  · simp [hr, hp0]
  · rcases m with _ | m
    · -- `m = 0`：拼接点取 `p n = y = q 0`。
      simp only [hr, Nat.add_zero, if_pos le_rfl]
      rw [hpn, ← hq0]
      exact hqm
    · have hnm : ¬n + (m + 1) ≤ n := by omega
      simp [hr, hnm, hqm]
  · have key : ∀ j ≤ m, r (n + j) = q j ∧ H.isPath r (n + j) := by
      intro j
      induction j with
      | zero =>
        intro _
        constructor
        · have hpn' : p n = q 0 := by rw [hpn, ← hq0]
          simp only [hr, Nat.add_zero, if_pos le_rfl]
          exact hpn'
        · have hcongr : H.isPath r n :=
            (H.isPath_congr (p := p) (p' := r) (fun k hk => by simp [hr, hk])).mp hp
          simpa using hcongr
      | succ j ih =>
        intro hjm
        obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le hjm)
        have hs : ¬n + (j + 1) ≤ n := by omega
        constructor
        · simp [hr, hs]
        · have hsucc : n + (j + 1) = n + j + 1 := by omega
          rw [hsucc, H.isPath_succ]
          refine ⟨h2, ?_⟩
          have hstep : H.goOneStep (q j) (q (j + 1)) := H.goOneStep_of_isPath hq hjm
          have hrj1 : r (n + j + 1) = q (j + 1) := by
            have hle : ¬n + j + 1 ≤ n := by omega
            have hsub : n + j + 1 - n = j + 1 := by omega
            simp [hr, hle, hsub]
          rw [h1, hrj1]
          exact hstep
    exact (key m le_rfl).2

end Hypermap

section OrbitSets

variable {α : Type*}

/-- `hypermap.hl`:157 `set_of_orbits`。 -/
def setOfOrbits (D : Finset α) (f : Equiv.Perm α) : Set (Set α) := {orbitMap f x | x ∈ D}

/-- `set_of_orbits` 有限（`D` 有限），故 `number_of_orbits` 的 `Set.ncard` 非平凡。 -/
theorem setOfOrbits_finite (D : Finset α) (f : Equiv.Perm α) : (setOfOrbits D f).Finite := by
  have h : setOfOrbits D f = (fun x => orbitMap f x) '' (D : Set α) := by
    ext t
    simp [setOfOrbits]
  rw [h]
  exact D.finite_toSet.image _

/-- `hypermap.hl`:161 `number_of_orbits`。 -/
noncomputable def numberOfOrbits (D : Finset α) (f : Equiv.Perm α) : ℕ :=
  (setOfOrbits D f).ncard

end OrbitSets

namespace Hypermap

variable {α : Type*} [DecidableEq α]

/-- `hypermap.hl`:163 `edge_set`。 -/
def edgeSet (H : Hypermap α) : Set (Set α) := setOfOrbits H.darts H.edgeMap

/-- `hypermap.hl`:165 `node_set`。 -/
def nodeSet (H : Hypermap α) : Set (Set α) := setOfOrbits H.darts H.nodeMap

/-- `hypermap.hl`:167 `face_set`。 -/
def faceSet (H : Hypermap α) : Set (Set α) := setOfOrbits H.darts H.faceMap

theorem edgeSet_finite (H : Hypermap α) : H.edgeSet.Finite :=
  setOfOrbits_finite H.darts H.edgeMap

theorem nodeSet_finite (H : Hypermap α) : H.nodeSet.Finite :=
  setOfOrbits_finite H.darts H.nodeMap

theorem faceSet_finite (H : Hypermap α) : H.faceSet.Finite :=
  setOfOrbits_finite H.darts H.faceMap

/-- `hypermap.hl`:169 `number_of_edges`（文件头注释中的新名为 `card_edge_set`）。 -/
noncomputable def numberOfEdges (H : Hypermap α) : ℕ := H.edgeSet.ncard

/-- `hypermap.hl`:171 `number_of_nodes`（新名 `card_node_set`）。 -/
noncomputable def numberOfNodes (H : Hypermap α) : ℕ := H.nodeSet.ncard

/-- `hypermap.hl`:173 `number_of_faces`（新名 `card_face_set`）。 -/
noncomputable def numberOfFaces (H : Hypermap α) : ℕ := H.faceSet.ncard

/-- `hypermap.hl`:149 `set_part_components`。 -/
def setPartComponents (H : Hypermap α) (D : Finset α) : Set (Set α) :=
  {H.combComponent x | x ∈ D}

/-- `hypermap.hl`:152 `set_of_components`。 -/
def setOfComponents (H : Hypermap α) : Set (Set α) := H.setPartComponents H.darts

theorem setPartComponents_finite (H : Hypermap α) (D : Finset α) :
    (H.setPartComponents D).Finite := by
  have h : H.setPartComponents D = (fun x => H.combComponent x) '' (D : Set α) := by
    ext t
    simp [setPartComponents]
  rw [h]
  exact D.finite_toSet.image _

theorem setOfComponents_finite (H : Hypermap α) : H.setOfComponents.Finite :=
  H.setPartComponents_finite H.darts

/-- `hypermap.hl`:175 `number_of_components`（新名 `card_set_of_components`）。 -/
noncomputable def numberOfComponents (H : Hypermap α) : ℕ := H.setOfComponents.ncard

/-- `hypermap.hl`:180 `plain_hypermap`。 -/
def Plain (H : Hypermap α) : Prop := H.edgeMap * H.edgeMap = 1

/-- `hypermap.hl`:182 `planar_hypermap`（Euler 公式）。 -/
def Planar (H : Hypermap α) : Prop :=
  H.numberOfNodes + H.numberOfEdges + H.numberOfFaces =
    H.darts.card + 2 * H.numberOfComponents

/-- `hypermap.hl`:186 `simple_hypermap`。 -/
def Simple (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, H.node x ∩ H.face x = {x}

/-- `hypermap.hl`:191 `dart_degenerate`。 -/
def DartDegenerate (H : Hypermap α) (x : α) : Prop :=
  H.edgeMap x = x ∨ H.nodeMap x = x ∨ H.faceMap x = x

/-- `hypermap.hl`:194 `dart_nondegenerate`。 -/
def DartNondegenerate (H : Hypermap α) (x : α) : Prop :=
  H.edgeMap x ≠ x ∧ H.nodeMap x ≠ x ∧ H.faceMap x ≠ x

/-- `hypermap.hl`:197 `is_edge_nondegenerate`。 -/
def EdgeNondegenerate (H : Hypermap α) : Prop := ∀ x ∈ H.darts, H.edgeMap x ≠ x

/-- `hypermap.hl`:200 `is_node_nondegenerate`。 -/
def NodeNondegenerate (H : Hypermap α) : Prop := ∀ x ∈ H.darts, H.nodeMap x ≠ x

/-- `hypermap.hl`:203 `is_face_nondegenerate`。 -/
def FaceNondegenerate (H : Hypermap α) : Prop := ∀ x ∈ H.darts, H.faceMap x ≠ x

end Hypermap

/-! ## 轨道迭代与有限阶（`hypermap.hl`:308–881 选摘） -/

section PermIteration

variable {α : Type*} {f : Equiv.Perm α} {s : Finset α} {x y z : α}

/-- `hypermap.hl`:321 `power_permutation`。 -/
theorem PermutesOn.pow (hf : PermutesOn f s) : ∀ n : ℕ, PermutesOn (f ^ n) s := by
  intro n
  induction n with
  | zero => intro x hx; simp
  | succ k ih => intro x hx; rw [pow_succ', Equiv.Perm.mul_apply, ih x hx, hf x hx]

/-- `f ^ m` 的不动点被任意次幂保持（`hypermap.hl`:255 `power_map_fix_point` 的幂形式）。 -/
theorem pow_fix_pow (f : Equiv.Perm α) {m : ℕ} (h : (f ^ m) x = x) :
    ∀ q : ℕ, ((f ^ m) ^ q) x = x := by
  intro q
  induction q with
  | zero => simp
  | succ q ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h]

/-- `hypermap.hl`:308 `orbit_cyclic`。 -/
theorem orbit_cyclic (f : Equiv.Perm α) {m : ℕ} (hm : m ≠ 0) (h : (f ^ m) x = x) :
    orbitMap f x = (fun k => (f ^ k) x) '' ↑(Finset.range m) := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    have key : (f ^ (n % m)) x = (f ^ n) x := by
      conv_rhs => rw [← Nat.mod_add_div n m]
      rw [pow_add, Equiv.Perm.mul_apply, pow_mul, pow_fix_pow f h]
    exact ⟨n % m, Finset.mem_range.mpr (Nat.mod_lt n (Nat.pos_of_ne_zero hm)), key⟩
  · rintro ⟨k, -, rfl⟩
    exact pow_apply_mem_orbitMap f k x

/-- `hypermap.hl`:876 `card_orbit_le`。 -/
theorem card_orbit_le (f : Equiv.Perm α) {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) x = x) :
    (orbitMap f x).ncard ≤ n := by
  rw [orbit_cyclic f hn h]
  calc ((fun k => (f ^ k) x) '' ↑(Finset.range n)).ncard
      ≤ (↑(Finset.range n) : Set ℕ).ncard :=
        Set.ncard_image_le (Finset.range n).finite_toSet
    _ = n := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- `hypermap.hl`:753 `finite_order`。
（经 `↥s` 上的诱导置换与有限群的 `pow_card_eq_one` 证明，取代 HOL 的
`inj_iterate_lemma` 鸽巢路线。） -/
theorem PermutesOn.exists_pow_eq_one (hf : PermutesOn f s) : ∃ n : ℕ, n ≠ 0 ∧ f ^ n = 1 := by
  classical
  have hiff : ∀ a : α, a ∈ s ↔ f a ∈ s :=
    fun a => ⟨hf.apply_mem, fun h => by
      by_contra ha
      exact ha ((hf a ha) ▸ h)⟩
  let fs : Equiv.Perm s := Equiv.subtypeEquiv f hiff
  have hpow : ∀ k : ℕ, ∀ a : ↥s, ((fs ^ k) a : α) = (f ^ k) a := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      calc ((fs ^ (k + 1)) a : α) = (fs ((fs ^ k) a) : α) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
        _ = f ((fs ^ k) a : α) := rfl
        _ = f ((f ^ k) a) := by rw [ih a]
        _ = (f ^ (k + 1)) a := by rw [pow_succ', Equiv.Perm.mul_apply]
  obtain ⟨n, hnpos, hn⟩ : ∃ n : ℕ, n ≠ 0 ∧ fs ^ n = 1 :=
    ⟨Fintype.card (Equiv.Perm ↥s),
      Nat.pos_iff_ne_zero.mp (Fintype.card_pos_iff.mpr ⟨1⟩), pow_card_eq_one⟩
  refine ⟨n, hnpos, ?_⟩
  ext x
  rw [Equiv.Perm.one_apply]
  by_cases hx : x ∈ s
  · have h1 : (fs ^ n) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hn]; rfl
    have h2 : (f ^ n) x = x := by
      have := hpow n ⟨x, hx⟩
      rw [h1] at this
      exact this.symm
    exact h2
  · exact hf.pow n x hx

/-- `hypermap.hl`:770 `inverse_element_lemma`。 -/
theorem PermutesOn.exists_pow_eq_inv (hf : PermutesOn f s) : ∃ j : ℕ, f⁻¹ = f ^ j := by
  obtain ⟨n, hn, hfn⟩ := hf.exists_pow_eq_one
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨k, ?_⟩
  have h1 : f * f ^ k = 1 := by rw [← pow_succ']; exact hfn
  exact (eq_inv_of_mul_eq_one_right h1).symm

/-- `hypermap.hl`:805 `inverse_relation`。 -/
theorem PermutesOn.exists_pow_apply_eq (hf : PermutesOn f s) (h : y = f x) :
    ∃ k : ℕ, x = (f ^ k) y := by
  obtain ⟨j, hj⟩ := hf.exists_pow_eq_inv
  refine ⟨j, ?_⟩
  have hx : x = f⁻¹ y := by
    rw [h, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [hj] at hx
  exact hx

/-- `hypermap.hl`:812 `power_power_relation`。 -/
theorem PermutesOn.exists_pow_apply_eq_of_pow (hf : PermutesOn f s) (h : (f ^ n) x = y) :
    ∃ j : ℕ, x = (f ^ j) y := by
  obtain ⟨j, hj⟩ := (hf.pow n).exists_pow_apply_eq h.symm
  exact ⟨n * j, by rw [pow_mul]; exact hj⟩

/-- `hypermap.hl`:366 `inverse_power_function`。 -/
theorem pow_apply_iff_inv_pow_apply (f : Equiv.Perm α) (n : ℕ) (x y : α) :
    y = (f ^ n) x ↔ x = (f⁻¹ ^ n) y := by
  rw [inv_pow]
  constructor
  · intro h
    rw [h, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  · intro h
    rw [h, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

/-- `hypermap.hl`:835 `orbit_sym`（有限支撑下逆向可达蕴含正向可达）。 -/
theorem orbitMap_sym (hf : PermutesOn f s) (h : x ∈ orbitMap f y) : y ∈ orbitMap f x := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨j, hj⟩ := hf.exists_pow_apply_eq_of_pow hn
  exact ⟨j, hj.symm⟩

/-- `hypermap.hl`:849 `orbit_trans`。 -/
theorem orbitMap_trans (h₁ : x ∈ orbitMap f y) (h₂ : y ∈ orbitMap f z) :
    x ∈ orbitMap f z := by
  obtain ⟨n, rfl⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, by rw [pow_add, Equiv.Perm.mul_apply, hm]⟩

/-- `hypermap.hl`:2123 `lemma_orbit_identity`（提前移植，供划分引理使用）。 -/
theorem orbitMap_eq_of_mem (hf : PermutesOn f s) (h : x ∈ orbitMap f y) :
    orbitMap f x = orbitMap f y := by
  ext t
  exact ⟨fun ht => orbitMap_trans ht h, fun ht => orbitMap_trans ht (orbitMap_sym hf h)⟩

/-- `hypermap.hl`:861 `partition_orbit`。 -/
theorem orbitMap_disjoint_or_eq (hf : PermutesOn f s) (x y : α) :
    orbitMap f x ∩ orbitMap f y = ∅ ∨ orbitMap f x = orbitMap f y := by
  by_cases h : (orbitMap f x ∩ orbitMap f y).Nonempty
  · obtain ⟨t, htx, hty⟩ := h
    exact Or.inr ((orbitMap_eq_of_mem hf htx).symm.trans (orbitMap_eq_of_mem hf hty))
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp h)

/-- `hypermap.hl`:1203 `lemma_orbit_convolution_map`。 -/
theorem orbitMap_of_mul_self_eq_one (h : f * f = 1) (x : α) :
    orbitMap f x = {x, f x} := by
  have h2 : (f ^ 2) x = x := by
    rw [pow_two, h, Equiv.Perm.one_apply]
  rw [orbit_cyclic f (m := 2) (by omega) h2]
  have hr : (Finset.range 2 : Finset ℕ) = {0, 1} := rfl
  rw [hr, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  have h0 : (f ^ 0) x = x := by simp
  have h1 : (f ^ 1) x = f x := by simp
  rw [h0, h1]

/-- `hypermap.hl`:1213 `lemma_nondegenerate_convolution`。 -/
theorem orbitMap_finite_ncard_two (hf : PermutesOn f s) (h2 : f * f = 1)
    (hfix : ∀ x ∈ s, f x ≠ x) (hx : x ∈ s) :
    (orbitMap f x).Finite ∧ (orbitMap f x).ncard = 2 :=
  ⟨orbitMap_finite hf x, by
    rw [orbitMap_of_mul_self_eq_one h2 x]
    exact Set.ncard_pair (hfix x hx).symm⟩

/-- `a * b * c = 1` 的轮换（`hypermap.hl`:887 `cyclic_maps` 的群论核心）。 -/
theorem perm_mul_eq_one_rotate {a b c : Equiv.Perm α} (h : a * b * c = 1) : b * c * a = 1 := by
  have h' : a * (b * c) = 1 := by rw [← mul_assoc]; exact h
  have hbc : b * c = a⁻¹ := eq_inv_of_mul_eq_one_right h'
  calc b * c * a = a⁻¹ * a := by rw [hbc]
    _ = 1 := inv_mul_cancel a

end PermIteration

/-- `hypermap.hl`:637 `glue`。两条路径的拼接：前 `n` 步走 `p`，之后走 `q`。 -/
def gluePaths {α : Type*} (p q : ℕ → α) (n : ℕ) : ℕ → α :=
  fun i => if i ≤ n then p i else q (i - n)

/-- `hypermap.hl`:642 `first_glue_evaluation`（含 :639 `start_glue_evaluation` 的 `i = 0` 情形）。 -/
theorem gluePaths_apply_le {α : Type*} {p q : ℕ → α} {n i : ℕ} (h : i ≤ n) :
    gluePaths p q n i = p i := if_pos h

/-- `hypermap.hl`:645 `second_glue_evaluation`。 -/
theorem gluePaths_apply_add {α : Type*} {p q : ℕ → α} {n : ℕ} (h : p n = q 0) (i : ℕ) :
    gluePaths p q n (n + i) = q i := by
  rcases i with _ | i
  · simp only [gluePaths, Nat.add_zero, if_pos le_rfl]
    exact h
  · have hle : ¬n + (i + 1) ≤ n := by omega
    simp [gluePaths, hle]

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `hypermap.hl`:374 `edge_map_inverse_representation`。 -/
theorem edgeMap_inverse_representation (H : Hypermap α) (x y : α) :
    y = H.edgeMap x ↔ x = H.edgeMap.symm y := by
  constructor
  · intro h; rw [h]; exact (Equiv.symm_apply_apply _ _).symm
  · intro h; rw [h]; exact (Equiv.apply_symm_apply _ _).symm

/-- `hypermap.hl`:379 `node_map_inverse_representation`。 -/
theorem nodeMap_inverse_representation (H : Hypermap α) (x y : α) :
    y = H.nodeMap x ↔ x = H.nodeMap.symm y := by
  constructor
  · intro h; rw [h]; exact (Equiv.symm_apply_apply _ _).symm
  · intro h; rw [h]; exact (Equiv.apply_symm_apply _ _).symm

/-- `hypermap.hl`:384 `face_map_inverse_representation`。 -/
theorem faceMap_inverse_representation (H : Hypermap α) (x y : α) :
    y = H.faceMap x ↔ x = H.faceMap.symm y := by
  constructor
  · intro h; rw [h]; exact (Equiv.symm_apply_apply _ _).symm
  · intro h; rw [h]; exact (Equiv.apply_symm_apply _ _).symm

/-- `hypermap.hl`:388 `node_map_injective`。 -/
theorem nodeMap_injective (H : Hypermap α) (x y : α) :
    H.nodeMap x = H.nodeMap y ↔ x = y := H.nodeMap.injective.eq_iff

/-- `hypermap.hl`:393 `face_map_injective`。 -/
theorem faceMap_injective (H : Hypermap α) (x y : α) :
    H.faceMap x = H.faceMap y ↔ x = y := H.faceMap.injective.eq_iff

/-- `hypermap.hl`:412 `lemma_dart_invariant`。 -/
theorem dart_invariant (H : Hypermap α) (hx : x ∈ H.darts) :
    H.edgeMap x ∈ H.darts ∧ H.nodeMap x ∈ H.darts ∧ H.faceMap x ∈ H.darts :=
  ⟨H.edgeMap_apply_mem hx, H.nodeMap_apply_mem hx, H.faceMap_apply_mem hx⟩

/-- `hypermap.hl`:415 `lemma_dart_invariant_power_node`。 -/
theorem dart_invariant_power_node (H : Hypermap α) (hx : x ∈ H.darts) (n : ℕ) :
    (H.nodeMap ^ n) x ∈ H.darts := H.nodeMap_permutes.pow_apply_mem n hx

/-- `hypermap.hl`:419 `lemma_dart_invariant_power_face`。 -/
theorem dart_invariant_power_face (H : Hypermap α) (hx : x ∈ H.darts) (n : ℕ) :
    (H.faceMap ^ n) x ∈ H.darts := H.faceMap_permutes.pow_apply_mem n hx

/-- `hypermap.hl`:423 `lemma_dart_inveriant_under_inverse_maps`（源文件名拼写如此）。 -/
theorem dart_invariant_under_inverse_maps (H : Hypermap α) (hx : x ∈ H.darts) :
    H.edgeMap.symm x ∈ H.darts ∧ H.nodeMap.symm x ∈ H.darts ∧ H.faceMap.symm x ∈ H.darts :=
  ⟨H.edgeMap_symm_apply_mem hx, H.nodeMap_symm_apply_mem hx, H.faceMap_symm_apply_mem hx⟩

/-- `hypermap.hl`:913 `hypermap_cyclic`。 -/
theorem hypermap_cyclic (H : Hypermap α) :
    H.nodeMap * H.faceMap * H.edgeMap = 1 ∧ H.faceMap * H.edgeMap * H.nodeMap = 1 :=
  ⟨perm_mul_eq_one_rotate H.comp_eq_one,
    perm_mul_eq_one_rotate (perm_mul_eq_one_rotate H.comp_eq_one)⟩

/-- `hypermap.hl`:923 `inverse_hypermap_maps`。 -/
theorem inverse_hypermap_maps (H : Hypermap α) :
    H.edgeMap⁻¹ = H.nodeMap * H.faceMap ∧ H.nodeMap⁻¹ = H.faceMap * H.edgeMap ∧
      H.faceMap⁻¹ = H.edgeMap * H.nodeMap := by
  refine ⟨H.nodeMap_mul_faceMap.symm, ?_, by rw [H.faceMap_eq_inv, inv_inv]⟩
  have h : H.nodeMap * (H.faceMap * H.edgeMap) = 1 := by
    rw [← mul_assoc]; exact H.hypermap_cyclic.1
  exact (eq_inv_of_mul_eq_one_right h).symm

/-- `hypermap.hl`:937 `inverse2_hypermap_maps`。 -/
theorem inverse2_hypermap_maps (H : Hypermap α) :
    H.edgeMap = H.faceMap⁻¹ * H.nodeMap⁻¹ ∧ H.nodeMap = H.edgeMap⁻¹ * H.faceMap⁻¹ ∧
      H.faceMap = H.nodeMap⁻¹ * H.edgeMap⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := H.inverse_hypermap_maps
  refine ⟨?_, ?_, ?_⟩
  · calc H.edgeMap = (H.edgeMap⁻¹)⁻¹ := (inv_inv _).symm
      _ = (H.nodeMap * H.faceMap)⁻¹ := by rw [h1]
      _ = H.faceMap⁻¹ * H.nodeMap⁻¹ := mul_inv_rev _ _
  · calc H.nodeMap = (H.nodeMap⁻¹)⁻¹ := (inv_inv _).symm
      _ = (H.faceMap * H.edgeMap)⁻¹ := by rw [h2]
      _ = H.edgeMap⁻¹ * H.faceMap⁻¹ := mul_inv_rev _ _
  · calc H.faceMap = (H.faceMap⁻¹)⁻¹ := (inv_inv _).symm
      _ = (H.edgeMap * H.nodeMap)⁻¹ := by rw [h3]
      _ = H.nodeMap⁻¹ * H.edgeMap⁻¹ := mul_inv_rev _ _

/-- `hypermap.hl`:1292 `lemma_def_path`。 -/
theorem isPath_iff (H : Hypermap α) (p : ℕ → α) (n : ℕ) :
    H.isPath p n ↔ ∀ i < n, H.goOneStep (p i) (p (i + 1)) := by
  constructor
  · intro h i hi
    exact H.goOneStep_of_isPath h (Nat.succ_le_of_lt hi)
  · intro h
    induction n with
    | zero => trivial
    | succ k ih =>
      rw [H.isPath_succ]
      exact ⟨ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)⟩

/-- `hypermap.hl`:1300 `edge_path`。 -/
def edgePath (H : Hypermap α) (x : α) (i : ℕ) : α := (H.edgeMap ^ i) x

/-- `hypermap.hl`:1303 `node_path`。 -/
def nodePath (H : Hypermap α) (x : α) (i : ℕ) : α := (H.nodeMap ^ i) x

/-- `hypermap.hl`:1306 `face_path`。 -/
def facePath (H : Hypermap α) (x : α) (i : ℕ) : α := (H.faceMap ^ i) x

theorem edgePath_zero (H : Hypermap α) (x : α) : H.edgePath x 0 = x := by simp [edgePath]

theorem nodePath_zero (H : Hypermap α) (x : α) : H.nodePath x 0 = x := by simp [nodePath]

theorem facePath_zero (H : Hypermap α) (x : α) : H.facePath x 0 = x := by simp [facePath]

/-- `hypermap.hl`:1309 `lemma_edge_path`。 -/
theorem isPath_edgePath (H : Hypermap α) (x : α) (k : ℕ) : H.isPath (H.edgePath x) k := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [H.isPath_succ]
    refine ⟨ih, Or.inl ?_⟩
    show (H.edgeMap ^ (k + 1)) x = H.edgeMap ((H.edgeMap ^ k) x)
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- `hypermap.hl`:1315 `lemma_node_path`。 -/
theorem isPath_nodePath (H : Hypermap α) (x : α) (k : ℕ) : H.isPath (H.nodePath x) k := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [H.isPath_succ]
    refine ⟨ih, Or.inr (Or.inl ?_)⟩
    show (H.nodeMap ^ (k + 1)) x = H.nodeMap ((H.nodeMap ^ k) x)
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- `hypermap.hl`:1321 `lemma_face_path`。 -/
theorem isPath_facePath (H : Hypermap α) (x : α) (k : ℕ) : H.isPath (H.facePath x) k := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [H.isPath_succ]
    refine ⟨ih, Or.inr (Or.inr ?_)⟩
    show (H.faceMap ^ (k + 1)) x = H.faceMap ((H.faceMap ^ k) x)
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- `hypermap.hl`:1263 `lemma_path_subset`。 -/
theorem path_mem_darts (H : Hypermap α) (hx : x ∈ H.darts) {p : ℕ → α} {n : ℕ}
    (hp0 : p 0 = x) (hp : H.isPath p n) : p n ∈ H.darts := by
  induction n with
  | zero => rw [hp0]; exact hx
  | succ k ih =>
    rw [H.isPath_succ] at hp
    rcases hp.2 with h | h | h
    · rw [h]; exact H.edgeMap_apply_mem (ih hp.1)
    · rw [h]; exact H.nodeMap_apply_mem (ih hp.1)
    · rw [h]; exact H.faceMap_apply_mem (ih hp.1)

/-- `hypermap.hl`:1272 `lemma_component_subset`。 -/
theorem combComponent_subset_darts (H : Hypermap α) (hx : x ∈ H.darts) :
    H.combComponent x ⊆ ↑H.darts := by
  rintro y ⟨p, n, hp0, hpn, hp⟩
  rw [← hpn]
  exact H.path_mem_darts hx hp0 hp

/-- `hypermap.hl`:1329 `lemma_glue_paths`。 -/
theorem isPath_gluePaths (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isPath p n) (hq : H.isPath q m) (h : p n = q 0) :
    H.isPath (gluePaths p q n) (n + m) := by
  rw [H.isPath_iff] at hp hq ⊢
  intro i hi
  by_cases hin : i < n
  · rw [gluePaths_apply_le hin.le, gluePaths_apply_le (by omega)]
    exact hp i hin
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = n + j := ⟨i - n, by omega⟩
    have h2 : gluePaths p q n (n + j + 1) = q (j + 1) := by
      rw [add_assoc]
      exact gluePaths_apply_add h (j + 1)
    rw [gluePaths_apply_add h j, h2]
    exact hq j (by omega)

/-- `hypermap.hl`:1351 `concatenate_two_paths`。 -/
theorem concatenate_two_paths (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isPath p n) (hq : H.isPath q m) (h : p n = q 0) :
    ∃ g : ℕ → α, g 0 = p 0 ∧ g (n + m) = q m ∧ H.isPath g (n + m) ∧
      (∀ i ≤ n, g i = p i) ∧ (∀ i ≤ m, g (n + i) = q i) :=
  ⟨gluePaths p q n, gluePaths_apply_le (Nat.zero_le n), gluePaths_apply_add h m,
    H.isPath_gluePaths hp hq h, fun _ hi => gluePaths_apply_le hi,
    fun i _ => gluePaths_apply_add h i⟩

/-- `hypermap.hl`:1360 `concatenate_paths`。 -/
theorem concatenate_paths (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isPath p n) (hq : H.isPath q m) (h : p n = q 0) :
    ∃ g : ℕ → α, g 0 = p 0 ∧ g (n + m) = q m ∧ H.isPath g (n + m) := by
  obtain ⟨g, h0, hm, hg, -, -⟩ := H.concatenate_two_paths hp hq h
  exact ⟨g, h0, hm, hg⟩

/-- `hypermap.hl`:1372 `lemma_reverse_path`。 -/
theorem reverse_path (H : Hypermap α) {p : ℕ → α} {n : ℕ} (hp : H.isPath p n) :
    ∃ q : ℕ → α, ∃ m : ℕ, q 0 = p n ∧ q m = p 0 ∧ H.isPath q m := by
  induction n with
  | zero => exact ⟨p, 0, rfl, rfl, hp⟩
  | succ k ih =>
    rw [H.isPath_succ] at hp
    obtain ⟨q, m, hq0, hqm, hq⟩ := ih hp.1
    rcases hp.2 with hstep | hstep | hstep
    · obtain ⟨j, hj⟩ := H.edgeMap_permutes.exists_pow_apply_eq hstep
      obtain ⟨g, hg0, hgm, hgpath, -, -⟩ :=
        H.concatenate_two_paths (H.isPath_edgePath (p (k + 1)) j) hq
          (hj.symm.trans hq0.symm)
      exact ⟨g, j + m, hg0.trans (H.edgePath_zero _), hgm.trans hqm, hgpath⟩
    · obtain ⟨j, hj⟩ := H.nodeMap_permutes.exists_pow_apply_eq hstep
      obtain ⟨g, hg0, hgm, hgpath, -, -⟩ :=
        H.concatenate_two_paths (H.isPath_nodePath (p (k + 1)) j) hq
          (hj.symm.trans hq0.symm)
      exact ⟨g, j + m, hg0.trans (H.nodePath_zero _), hgm.trans hqm, hgpath⟩
    · obtain ⟨j, hj⟩ := H.faceMap_permutes.exists_pow_apply_eq hstep
      obtain ⟨g, hg0, hgm, hgpath, -, -⟩ :=
        H.concatenate_two_paths (H.isPath_facePath (p (k + 1)) j) hq
          (hj.symm.trans hq0.symm)
      exact ⟨g, j + m, hg0.trans (H.facePath_zero _), hgm.trans hqm, hgpath⟩

/-- `hypermap.hl`:1417 `lemma_component_symmetry` 的 `isInComponent` 形式。 -/
theorem isInComponent_symm (H : Hypermap α) (h : H.isInComponent x y) :
    H.isInComponent y x := by
  obtain ⟨p, n, hp0, hpn, hp⟩ := h
  obtain ⟨q, m, hq0, hqm, hq⟩ := H.reverse_path hp
  exact ⟨q, m, hq0.trans hpn, hqm.trans hp0, hq⟩

/-- `hypermap.hl`:1417 `lemma_component_symmetry`。 -/
theorem combComponent_symmetry (H : Hypermap α) (h : y ∈ H.combComponent x) :
    x ∈ H.combComponent y := H.isInComponent_symm h

/-- `is_in_component` 是等价关系（`hypermap.hl` 中 refl/symmetry/trans 三引理的闭环）。 -/
theorem isInComponent_equivalence (H : Hypermap α) : Equivalence H.isInComponent :=
  ⟨H.isInComponent_refl, H.isInComponent_symm, H.isInComponent_trans⟩

/-- `hypermap.hl`:1423 `partition_components`。 -/
theorem partition_components (H : Hypermap α) (x y : α) :
    H.combComponent x = H.combComponent y ∨ H.combComponent x ∩ H.combComponent y = ∅ := by
  by_cases h : (H.combComponent x ∩ H.combComponent y).Nonempty
  · obtain ⟨t, htx, hty⟩ := h
    left
    ext u
    constructor
    · intro hu
      exact H.isInComponent_trans (H.isInComponent_trans hty (H.isInComponent_symm htx)) hu
    · intro hu
      exact H.isInComponent_trans (H.isInComponent_trans htx (H.isInComponent_symm hty)) hu
  · right
    exact Set.not_nonempty_iff_eq_empty.mp h

/-- dart 集合外的点自成组件（`hypermap.hl` 组件计数理论中 `FINITE` 前提的来源之一）。 -/
theorem combComponent_eq_singleton_of_not_mem (H : Hypermap α) (hx : x ∉ H.darts) :
    H.combComponent x = {x} := by
  ext y
  constructor
  · rintro ⟨p, n, hp0, hpn, hp⟩
    have key : ∀ i ≤ n, p i = x := by
      intro i
      induction i with
      | zero => intro _; exact hp0
      | succ k ih =>
        intro hkn
        have hk : p k = x := ih (Nat.le_of_succ_le hkn)
        rcases H.goOneStep_of_isPath hp hkn with h | h | h
        · rw [h, hk, H.edgeMap_permutes x hx]
        · rw [h, hk, H.nodeMap_permutes x hx]
        · rw [h, hk, H.faceMap_permutes x hx]
    rw [Set.mem_singleton_iff, ← hpn]
    exact key n le_rfl
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact H.mem_combComponent_self x

/-- 组合组件有限（`hypermap.hl` 组件计数的前提）。 -/
theorem combComponent_finite (H : Hypermap α) (x : α) : (H.combComponent x).Finite := by
  by_cases hx : x ∈ H.darts
  · exact H.darts.finite_toSet.subset (H.combComponent_subset_darts hx)
  · rw [H.combComponent_eq_singleton_of_not_mem hx]
    exact Set.finite_singleton x

/-- `hypermap.hl`:1439 `lemma_partition_by_components`。 -/
theorem sUnion_setOfComponents (H : Hypermap α) : ↑H.darts = ⋃₀ H.setOfComponents := by
  ext x
  rw [Set.mem_sUnion]
  constructor
  · intro hx
    exact ⟨H.combComponent x, ⟨x, hx, rfl⟩, H.mem_combComponent_self x⟩
  · rintro ⟨t, ⟨y, hy, rfl⟩, hxt⟩
    exact H.combComponent_subset_darts hy hxt

end Hypermap

/-! ## 轨道计数（`hypermap.hl`:1051–1201 选摘） -/

section OrbitCounting

variable {α : Type*} {f : Equiv.Perm α} {s : Finset α} {x : α}

/-- `hypermap.hl`:1060 `lemma_partition`。 -/
theorem sUnion_setOfOrbits (hf : PermutesOn f s) : (↑s : Set α) = ⋃₀ setOfOrbits s f := by
  ext x
  rw [Set.mem_sUnion]
  constructor
  · intro hx
    exact ⟨orbitMap f x, ⟨x, hx, rfl⟩, mem_orbitMap_self f x⟩
  · rintro ⟨t, ⟨y, hy, rfl⟩, hxt⟩
    exact orbitMap_subset_of_permutesOn hf hy hxt

/-- `hypermap.hl`:1146 `card_partition_formula`
（`lemma_card_of_disjoint_covering`（1067）由 Mathlib 的 `Set.Finite.ncard_biUnion` 替代）。 -/
theorem ncard_eq_finsum_orbits (hf : PermutesOn f s) :
    (↑s : Set α).ncard = ∑ᶠ u ∈ setOfOrbits s f, u.ncard := by
  have hfin : (setOfOrbits s f).Finite := setOfOrbits_finite s f
  have hfin' : ∀ u ∈ setOfOrbits s f, u.Finite := by
    intro u hu
    obtain ⟨x, -, rfl⟩ := hu
    exact orbitMap_finite hf x
  have hdisj : (setOfOrbits s f).PairwiseDisjoint id := by
    intro u hu v hv hne
    obtain ⟨x, -, rfl⟩ := hu
    obtain ⟨y, -, rfl⟩ := hv
    rcases orbitMap_disjoint_or_eq hf x y with h | h
    · exact Set.disjoint_iff_inter_eq_empty.mpr h
    · exact absurd h hne
  calc (↑s : Set α).ncard = (⋃₀ setOfOrbits s f).ncard := by rw [sUnion_setOfOrbits hf]
    _ = (⋃ u ∈ setOfOrbits s f, u).ncard := by rw [Set.sUnion_eq_biUnion]
    _ = ∑ᶠ u ∈ setOfOrbits s f, u.ncard := hfin.ncard_biUnion hfin' hdisj

/-- `hypermap.hl`:1185 `lemma_card_eq`。 -/
theorem ncard_eq_mul_numberOfOrbits (hf : PermutesOn f s) {m : ℕ}
    (h : ∀ x ∈ s, (orbitMap f x).ncard = m) :
    (↑s : Set α).ncard = m * numberOfOrbits s f := by
  classical
  have hfin := setOfOrbits_finite s f
  rw [ncard_eq_finsum_orbits hf, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsum : ∀ u ∈ hfin.toFinset, u.ncard = m := by
    intro u hu
    rw [hfin.mem_toFinset] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact h x hx
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul]
  have hcard : numberOfOrbits s f = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hcard, Nat.mul_comm]

/-- `hypermap.hl`:1167 `lemma_card_lower_bound`。 -/
theorem mul_numberOfOrbits_le_ncard (hf : PermutesOn f s) {m : ℕ}
    (h : ∀ x ∈ s, m ≤ (orbitMap f x).ncard) :
    m * numberOfOrbits s f ≤ (↑s : Set α).ncard := by
  classical
  have hfin := setOfOrbits_finite s f
  rw [ncard_eq_finsum_orbits hf, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsum : ∀ u ∈ hfin.toFinset, m ≤ u.ncard := by
    intro u hu
    rw [hfin.mem_toFinset] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact h x hx
  have hcard : m * numberOfOrbits s f = ∑ u ∈ hfin.toFinset, m := by
    rw [Finset.sum_const, smul_eq_mul]
    have hc : numberOfOrbits s f = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
    rw [hc, Nat.mul_comm]
  rw [hcard]
  exact Finset.sum_le_sum hsum

end OrbitCounting

namespace Hypermap

variable {α : Type*} [DecidableEq α]

/-- `hypermap.hl`:1000 `connected_hypermap`。 -/
def Connected (H : Hypermap α) : Prop := H.numberOfComponents = 1

/-- `hypermap.hl`:1228 `lemmaTGJISOK`：连通 + plain + planar 且边非退化、节点度数 ≥ 3
的 hypermap 中 dart 数的上界（Euler 公式的推论）。 -/
theorem darts_card_le (H : Hypermap α) (hconn : H.Connected) (hplain : H.Plain)
    (hplanar : H.Planar)
    (hnondeg : ∀ x ∈ H.darts, H.edgeMap x ≠ x ∧ 3 ≤ (H.node x).ncard) :
    H.darts.card ≤ 6 * H.numberOfFaces - 12 := by
  have hedge : ∀ x ∈ H.darts, (H.edge x).ncard = 2 := fun x hx =>
    (orbitMap_finite_ncard_two H.edgeMap_permutes hplain (fun y hy => (hnondeg y hy).1) hx).2
  have hD : H.darts.card = 2 * H.numberOfEdges := by
    have h := ncard_eq_mul_numberOfOrbits H.edgeMap_permutes hedge
    rwa [Set.ncard_coe_finset] at h
  have hN : 3 * H.numberOfNodes ≤ H.darts.card := by
    have h := mul_numberOfOrbits_le_ncard H.nodeMap_permutes (fun x hx => (hnondeg x hx).2)
    rwa [Set.ncard_coe_finset] at h
  unfold Connected at hconn
  unfold Planar at hplanar
  omega

end Hypermap

/-! ## Contour paths（`hypermap.hl`:1453–1628） -/

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `hypermap.hl`:1455 `one_step_contour`：沿 `faceMap` 一步或沿 `nodeMap.symm` 一步。 -/
def oneStepContour (H : Hypermap α) (x y : α) : Prop :=
  y = H.faceMap x ∨ y = H.nodeMap.symm x

/-- `hypermap.hl`:1457 `is_contour`。 -/
def isContour (H : Hypermap α) (p : ℕ → α) : ℕ → Prop
  | 0 => True
  | n + 1 => isContour H p n ∧ oneStepContour H (p n) (p (n + 1))

theorem isContour_succ (H : Hypermap α) (p : ℕ → α) (n : ℕ) :
    H.isContour p (n + 1) ↔ H.isContour p n ∧ H.oneStepContour (p n) (p (n + 1)) := Iff.rfl

/-- `hypermap.hl`:1460 `lemma_subcontour`。 -/
theorem isContour_mono (H : Hypermap α) {p : ℕ → α} {n m : ℕ}
    (h : H.isContour p n) (hmn : m ≤ n) : H.isContour p m := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hmn
    exact h
  | succ k ih =>
    rw [H.isContour_succ] at h
    rcases (by omega : m ≤ k ∨ m = k + 1) with hle | heq
    · exact ih h.1 hle
    · subst heq
      exact (H.isContour_succ p k).mpr h

/-- 长 contour 的第 `j` 步是合法步（`j + 1 ≤ n`）。 -/
theorem oneStepContour_of_isContour (H : Hypermap α) {p : ℕ → α} {n j : ℕ}
    (h : H.isContour p n) (hj : j + 1 ≤ n) : H.oneStepContour (p j) (p (j + 1)) :=
  ((H.isContour_succ p j).mp (H.isContour_mono h hj)).2

/-- `hypermap.hl`:1468 `lemma_def_contour`。 -/
theorem isContour_iff (H : Hypermap α) (p : ℕ → α) (n : ℕ) :
    H.isContour p n ↔ ∀ i < n, H.oneStepContour (p i) (p (i + 1)) := by
  constructor
  · intro h i hi
    exact H.oneStepContour_of_isContour h (Nat.succ_le_of_lt hi)
  · intro h
    induction n with
    | zero => trivial
    | succ k ih =>
      rw [H.isContour_succ]
      exact ⟨ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)⟩

/-- `hypermap.hl`:1473 `lemma_glue_contours`。 -/
theorem isContour_gluePaths (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isContour p n) (hq : H.isContour q m) (h : p n = q 0) :
    H.isContour (gluePaths p q n) (n + m) := by
  rw [H.isContour_iff] at hp hq ⊢
  intro i hi
  by_cases hin : i < n
  · rw [gluePaths_apply_le hin.le, gluePaths_apply_le (by omega)]
    exact hp i hin
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = n + j := ⟨i - n, by omega⟩
    have h2 : gluePaths p q n (n + j + 1) = q (j + 1) := by
      rw [add_assoc]
      exact gluePaths_apply_add h (j + 1)
    rw [gluePaths_apply_add h j, h2]
    exact hq j (by omega)

/-- `hypermap.hl`:1495 `concatenate_contours`。 -/
theorem concatenate_contours (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isContour p n) (hq : H.isContour q m) (h : p n = q 0) :
    ∃ g : ℕ → α, g 0 = p 0 ∧ g (n + m) = q m ∧ H.isContour g (n + m) ∧
      (∀ i ≤ n, g i = p i) ∧ (∀ i ≤ m, g (n + i) = q i) :=
  ⟨gluePaths p q n, gluePaths_apply_le (Nat.zero_le n), gluePaths_apply_add h m,
    H.isContour_gluePaths hp hq h, fun _ hi => gluePaths_apply_le hi,
    fun i _ => gluePaths_apply_add h i⟩

/-- `hypermap.hl`:1508 `node_contour`。 -/
def nodeContour (H : Hypermap α) (x : α) (i : ℕ) : α := (H.nodeMap.symm ^ i) x

/-- `hypermap.hl`:1512 `face_contour`（即 `face_path`）。 -/
def faceContour (H : Hypermap α) (x : α) (i : ℕ) : α := (H.faceMap ^ i) x

theorem nodeContour_zero (H : Hypermap α) (x : α) : H.nodeContour x 0 = x := by
  simp [nodeContour]

theorem faceContour_zero (H : Hypermap α) (x : α) : H.faceContour x 0 = x := by
  simp [faceContour]

/-- `hypermap.hl`:1514 `lemma_node_contour`。 -/
theorem isContour_nodeContour (H : Hypermap α) (x : α) (k : ℕ) :
    H.isContour (H.nodeContour x) k := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [H.isContour_succ]
    refine ⟨ih, Or.inr ?_⟩
    show (H.nodeMap.symm ^ (k + 1)) x = H.nodeMap.symm ((H.nodeMap.symm ^ k) x)
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- `hypermap.hl`:1522 `lemma_face_contour`。 -/
theorem isContour_faceContour (H : Hypermap α) (x : α) (k : ℕ) :
    H.isContour (H.faceContour x) k := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [H.isContour_succ]
    refine ⟨ih, Or.inl ?_⟩
    show (H.faceMap ^ (k + 1)) x = H.faceMap ((H.faceMap ^ k) x)
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- `hypermap.hl`:1530 `existence_contour`：任意 path 可改写为同端点的 contour。
（证明路线与 HOL 不同：edge 步 = `nodeMap.symm` 一步 + `faceMap` 的幂；
node 步 = `nodeMap.symm` 的幂，均来自有限阶。） -/
theorem existence_contour (H : Hypermap α) {p : ℕ → α} {n : ℕ} (hp : H.isPath p n) :
    ∃ q : ℕ → α, ∃ m : ℕ, q 0 = p 0 ∧ q m = p n ∧ H.isContour q m := by
  induction n with
  | zero => exact ⟨p, 0, rfl, rfl, trivial⟩
  | succ k ih =>
    rw [H.isPath_succ] at hp
    obtain ⟨q, m, hq0, hqm, hq⟩ := ih hp.1
    rcases hp.2 with hstep | hstep | hstep
    · -- edge 步：`p (k+1) = edgeMap (p k)`，拆为 `nodeMap.symm` 一步 + `faceMap ^ j`。
      obtain ⟨j, hj⟩ := H.faceMap_permutes.exists_pow_eq_inv
      have h1 : H.edgeMap (p k) = (H.faceMap ^ j) (H.nodeMap⁻¹ (p k)) := by
        rw [H.inverse2_hypermap_maps.1, Equiv.Perm.mul_apply, hj]
      obtain ⟨g1, hg10, hg1m, hg1c, -, -⟩ :=
        H.concatenate_contours hq (H.isContour_nodeContour (q m) 1)
          (H.nodeContour_zero (q m)).symm
      have hg1v : g1 (m + 1) = H.nodeMap.symm (q m) := by
        rw [hg1m]
        show (H.nodeMap.symm ^ 1) (q m) = H.nodeMap.symm (q m)
        simp
      obtain ⟨g2, hg20, hg2m, hg2c, -, -⟩ :=
        H.concatenate_contours hg1c (H.isContour_faceContour (H.nodeMap.symm (q m)) j)
          (by rw [hg1v]; exact (H.faceContour_zero _).symm)
      refine ⟨g2, m + 1 + j, hg20.trans (hg10.trans hq0), ?_, hg2c⟩
      rw [hg2m]
      show (H.faceMap ^ j) (H.nodeMap.symm (q m)) = p (k + 1)
      rw [hqm]
      exact (hstep.trans h1).symm
    · -- node 步：`p (k+1) = nodeMap (p k)`，即 `p (k+1) = (nodeMap.symm ^ j) (p k)`。
      have hback : p k = H.nodeMap.symm (p (k + 1)) := by
        rw [hstep]; exact (Equiv.symm_apply_apply _ _).symm
      obtain ⟨j, hj⟩ := H.nodeMap_permutes.symm.exists_pow_apply_eq hback
      obtain ⟨g, hg0, hgm, hgc, -, -⟩ :=
        H.concatenate_contours hq (H.isContour_nodeContour (q m) j)
          (H.nodeContour_zero (q m)).symm
      refine ⟨g, m + j, hg0.trans hq0, ?_, hgc⟩
      rw [hgm, hqm]
      show (H.nodeMap.symm ^ j) (p k) = p (k + 1)
      exact hj.symm
    · -- face 步：一步 `faceContour`。
      obtain ⟨g, hg0, hgm, hgc, -, -⟩ :=
        H.concatenate_contours hq (H.isContour_faceContour (q m) 1)
          (H.faceContour_zero (q m)).symm
      refine ⟨g, m + 1, hg0.trans hq0, ?_, hgc⟩
      rw [hgm, hqm]
      show (H.faceMap ^ 1) (p k) = p (k + 1)
      rw [pow_one]
      exact hstep.symm

/-- `hypermap.hl`:1597 `is_inj_contour`。 -/
def isInjContour (H : Hypermap α) (p : ℕ → α) : ℕ → Prop
  | 0 => True
  | n + 1 => isInjContour H p n ∧ oneStepContour H (p n) (p (n + 1)) ∧
      (∀ i ≤ n, p i ≠ p (n + 1))

theorem isInjContour_succ (H : Hypermap α) (p : ℕ → α) (n : ℕ) :
    H.isInjContour p (n + 1) ↔ H.isInjContour p n ∧ H.oneStepContour (p n) (p (n + 1)) ∧
      (∀ i ≤ n, p i ≠ p (n + 1)) := Iff.rfl

/-- `hypermap.hl`:1601 `lemma_sub_inj_contour`。 -/
theorem isInjContour_mono (H : Hypermap α) {p : ℕ → α} {n m : ℕ}
    (h : H.isInjContour p n) (hmn : m ≤ n) : H.isInjContour p m := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hmn
    exact h
  | succ k ih =>
    rw [H.isInjContour_succ] at h
    rcases (by omega : m ≤ k ∨ m = k + 1) with hle | heq
    · exact ih h.1 hle
    · subst heq
      exact (H.isInjContour_succ p k).mpr h

theorem isContour_of_isInjContour (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (h : H.isInjContour p n) : H.isContour p n := by
  induction n with
  | zero => trivial
  | succ k ih =>
    rw [H.isInjContour_succ] at h
    exact (H.isContour_succ p k).mpr ⟨ih h.1, h.2.1⟩

/-- `hypermap.hl`:1608 `lemma_def_inj_contour`。 -/
theorem isInjContour_iff (H : Hypermap α) (p : ℕ → α) (n : ℕ) :
    H.isInjContour p n ↔
      H.isContour p n ∧ (∀ i j : ℕ, i ≤ n → j < i → p j ≠ p i) := by
  constructor
  · intro h
    induction n with
    | zero => exact ⟨trivial, fun i j hi hj => by omega⟩
    | succ k ih =>
      rw [H.isInjContour_succ] at h
      obtain ⟨hcont, hinj⟩ := ih h.1
      refine ⟨(H.isContour_succ p k).mpr ⟨hcont, h.2.1⟩, fun i j hi hj => ?_⟩
      rcases (by omega : i ≤ k ∨ i = k + 1) with hik | rfl
      · exact hinj i j hik hj
      · exact h.2.2 j (by omega)
  · rintro ⟨hcont, hinj⟩
    induction n with
    | zero => trivial
    | succ k ih =>
      rw [H.isInjContour_succ]
      refine ⟨ih (H.isContour_mono hcont k.le_succ) (fun i j hi hj => hinj i j
        (hi.trans k.le_succ) hj), (H.isContour_succ p k).mp hcont |>.2, fun i hi => ?_⟩
      exact hinj (k + 1) i (by omega) (by omega)

end Hypermap

/-! ## Walkup 基础（`hypermap.hl`:1632–1978） -/

/-- `hypermap.hl`:1854 `fixed_point_lemma`。 -/
theorem Perm_apply_eq_self_iff_symm {α : Type*} (f : Equiv.Perm α) (x : α) :
    f x = x ↔ f.symm x = x := by
  constructor
  · intro h
    calc f.symm x = f.symm (f x) := by rw [h]
      _ = x := f.symm_apply_apply x
  · intro h
    calc f x = f (f.symm x) := by rw [h]
      _ = x := f.apply_symm_apply x

/-- `hypermap.hl`:1864 `non_fixed_point_lemma`。 -/
theorem Perm_apply_ne_self_iff_symm {α : Type*} (f : Equiv.Perm α) (x : α) :
    f x ≠ x ↔ f.symm x ≠ x := not_congr (Perm_apply_eq_self_iff_symm f x)

/-- `hypermap.hl`:1748 `PERMUTES_COMPOSITION`。 -/
theorem PermutesOn.mul {α : Type*} {f g : Equiv.Perm α} {s : Finset α}
    (hf : PermutesOn f s) (hg : PermutesOn g s) : PermutesOn (f * g) s := by
  intro x hx
  rw [Equiv.Perm.mul_apply, hg x hx, hf x hx]

/-- `hypermap.hl`:1733 `walkup_permutes`。 -/
theorem PermutesOn.swap_mul_erase {α : Type*} [DecidableEq α] {f : Equiv.Perm α} {s : Finset α}
    (hf : PermutesOn f s) (x : α) :
    PermutesOn (Equiv.swap x (f x) * f) (s.erase x) := by
  intro y hy
  have hyx : y = x ∨ y ∉ s := by
    by_cases h : y = x
    · exact Or.inl h
    · exact Or.inr (fun hys => hy (Finset.mem_erase.mpr ⟨h, hys⟩))
  rcases hyx with rfl | hys
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  · by_cases hyx : y = x
    · subst hyx
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    · rw [Equiv.Perm.mul_apply, hf y hys,
        Equiv.swap_apply_of_ne_of_ne hyx (fun hyfx => hyx (f.injective (by
          rw [← hyfx, hf y hys])))]

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `hypermap.hl`:1632 `isolated_dart`。 -/
def IsolatedDart (H : Hypermap α) (x : α) : Prop :=
  H.edgeMap x = x ∧ H.nodeMap x = x ∧ H.faceMap x = x

/-- `hypermap.hl`:1634 `is_edge_degenerate`。 -/
def IsEdgeDegenerate (H : Hypermap α) (x : α) : Prop :=
  H.edgeMap x = x ∧ H.nodeMap x ≠ x ∧ H.faceMap x ≠ x

/-- `hypermap.hl`:1637 `is_node_degenerate`。 -/
def IsNodeDegenerate (H : Hypermap α) (x : α) : Prop :=
  H.edgeMap x ≠ x ∧ H.nodeMap x = x ∧ H.faceMap x ≠ x

/-- `hypermap.hl`:1640 `is_face_degenerate`。 -/
def IsFaceDegenerate (H : Hypermap α) (x : α) : Prop :=
  H.edgeMap x ≠ x ∧ H.nodeMap x ≠ x ∧ H.faceMap x = x

/-- `hypermap.hl`:1644 `degenerate_lemma`。 -/
theorem dartDegenerate_iff (H : Hypermap α) (x : α) :
    H.DartDegenerate x ↔ H.IsolatedDart x ∨ H.IsEdgeDegenerate x ∨
      H.IsNodeDegenerate x ∨ H.IsFaceDegenerate x := by
  -- 任意两个映射固定 `x` ⟹ 第三个也固定（由三条逆映射等式 + `fixed_point_lemma`）
  have fix_of_two {a b c : Equiv.Perm α} (hinv : a⁻¹ = b * c)
      (hb : b x = x) (hc : c x = x) : a x = x := by
    have h1 : a⁻¹ x = x := by rw [hinv, Equiv.Perm.mul_apply, hc, hb]
    have h2 : a = a⁻¹.symm := rfl
    rw [h2]
    exact (Perm_apply_eq_self_iff_symm a⁻¹ x).mp h1
  have fixF : H.edgeMap x = x → H.nodeMap x = x → H.faceMap x = x :=
    fix_of_two H.inverse_hypermap_maps.2.2
  have fixN : H.edgeMap x = x → H.faceMap x = x → H.nodeMap x = x :=
    fun he hf => fix_of_two H.inverse_hypermap_maps.2.1 hf he
  have fixE : H.nodeMap x = x → H.faceMap x = x → H.edgeMap x = x :=
    fix_of_two H.inverse_hypermap_maps.1
  constructor
  · rintro (he | hn | hf)
    · by_cases hn : H.nodeMap x = x
      · by_cases hf : H.faceMap x = x
        · exact Or.inl ⟨he, hn, hf⟩
        · exact absurd (fixF he hn) hf
      · by_cases hf : H.faceMap x = x
        · exact absurd (fixN he hf) hn
        · exact Or.inr (Or.inl ⟨he, hn, hf⟩)
    · by_cases he : H.edgeMap x = x
      · by_cases hf : H.faceMap x = x
        · exact Or.inl ⟨he, hn, hf⟩
        · exact absurd (fixF he hn) hf
      · by_cases hf : H.faceMap x = x
        · exact absurd (fixE hn hf) he
        · exact Or.inr (Or.inr (Or.inl ⟨he, hn, hf⟩))
    · by_cases he : H.edgeMap x = x
      · by_cases hn : H.nodeMap x = x
        · exact Or.inl ⟨he, hn, hf⟩
        · exact absurd (fixN he hf) hn
      · by_cases hn : H.nodeMap x = x
        · exact absurd (fixE hn hf) he
        · exact Or.inr (Or.inr (Or.inr ⟨he, hn, hf⟩))
  · rintro (⟨he, -, -⟩ | ⟨he, -, -⟩ | ⟨-, hn, -⟩ | ⟨-, -, hf⟩)
    · exact Or.inl he
    · exact Or.inl he
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr hf)

/-- `hypermap.hl`:1670 `lemma_category_darts`。 -/
theorem dartNondegenerate_or_dartDegenerate (H : Hypermap α) (x : α) :
    H.DartNondegenerate x ∨ H.DartDegenerate x := by
  by_cases he : H.edgeMap x = x
  · exact Or.inr (Or.inl he)
  · by_cases hn : H.nodeMap x = x
    · exact Or.inr (Or.inr (Or.inl hn))
    · by_cases hf : H.faceMap x = x
      · exact Or.inr (Or.inr (Or.inr hf))
      · exact Or.inl ⟨he, hn, hf⟩

/-- `hypermap.hl`:1706 `shift`：轮换三个映射的角色（`hypermap_cyclic` 保证仍是 hypermap）。 -/
def shift (H : Hypermap α) : Hypermap α where
  darts := H.darts
  edgeMap := H.nodeMap
  nodeMap := H.faceMap
  faceMap := H.edgeMap
  edgeMap_permutes := H.nodeMap_permutes
  nodeMap_permutes := H.faceMap_permutes
  faceMap_permutes := H.edgeMap_permutes
  comp_eq_one := H.hypermap_cyclic.1

/-- `hypermap.hl`:1708 `shift_lemma`。 -/
theorem shift_lemma (H : Hypermap α) :
    H.darts = H.shift.darts ∧ H.edgeMap = H.shift.faceMap ∧
      H.nodeMap = H.shift.edgeMap ∧ H.faceMap = H.shift.nodeMap :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `hypermap.hl`:1715 `double_shift_lemma`。 -/
theorem double_shift_lemma (H : Hypermap α) :
    H.darts = H.shift.shift.darts ∧ H.edgeMap = H.shift.shift.nodeMap ∧
      H.nodeMap = H.shift.shift.faceMap ∧ H.faceMap = H.shift.shift.edgeMap :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `hypermap.hl`:1721 `edge_walkup`：删去 dart `x` 并把其邻接关系"短路"的 hypermap。 -/
def edgeWalkup (H : Hypermap α) (x : α) : Hypermap α where
  darts := H.darts.erase x
  edgeMap := (Equiv.swap x (H.faceMap x) * H.faceMap)⁻¹ *
    (Equiv.swap x (H.nodeMap x) * H.nodeMap)⁻¹
  nodeMap := Equiv.swap x (H.nodeMap x) * H.nodeMap
  faceMap := Equiv.swap x (H.faceMap x) * H.faceMap
  edgeMap_permutes :=
    (H.faceMap_permutes.swap_mul_erase x).symm.mul (H.nodeMap_permutes.swap_mul_erase x).symm
  nodeMap_permutes := H.nodeMap_permutes.swap_mul_erase x
  faceMap_permutes := H.faceMap_permutes.swap_mul_erase x
  comp_eq_one := by
    generalize Equiv.swap x (H.faceMap x) * H.faceMap = F
    generalize Equiv.swap x (H.nodeMap x) * H.nodeMap = N
    rw [mul_assoc F⁻¹ N⁻¹ N, inv_mul_cancel, mul_one, inv_mul_cancel]

/-- `hypermap.hl`:1723 `node_walkup`。 -/
def nodeWalkup (H : Hypermap α) (x : α) : Hypermap α := (H.shift.edgeWalkup x).shift.shift

/-- `hypermap.hl`:1725 `face_walkup`。 -/
def faceWalkup (H : Hypermap α) (x : α) : Hypermap α := (H.shift.shift.edgeWalkup x).shift

/-- `hypermap.hl`:1727 `double_edge_walkup`。 -/
def doubleEdgeWalkup (H : Hypermap α) (x y : α) : Hypermap α := (H.edgeWalkup x).edgeWalkup y

/-- `hypermap.hl`:1729 `double_node_walkup`。 -/
def doubleNodeWalkup (H : Hypermap α) (x y : α) : Hypermap α := (H.nodeWalkup x).nodeWalkup y

/-- `hypermap.hl`:1731 `double_face_walkup`。 -/
def doubleFaceWalkup (H : Hypermap α) (x y : α) : Hypermap α := (H.faceWalkup x).faceWalkup y

/-- `hypermap.hl`:1751 `lemma_edge_walkup`（structure 编码下即定义展开）。 -/
theorem lemma_edge_walkup (H : Hypermap α) (x : α) :
    (H.edgeWalkup x).darts = H.darts.erase x ∧
    (H.edgeWalkup x).edgeMap = (Equiv.swap x (H.faceMap x) * H.faceMap)⁻¹ *
      (Equiv.swap x (H.nodeMap x) * H.nodeMap)⁻¹ ∧
    (H.edgeWalkup x).nodeMap = Equiv.swap x (H.nodeMap x) * H.nodeMap ∧
    (H.edgeWalkup x).faceMap = Equiv.swap x (H.faceMap x) * H.faceMap :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `hypermap.hl`:1781 `node_map_walkup`。 -/
theorem nodeMap_walkup (H : Hypermap α) (x y : α) :
    (H.edgeWalkup x).nodeMap x = x ∧
    (H.edgeWalkup x).nodeMap (H.nodeMap.symm x) = H.nodeMap x ∧
    (y ≠ x ∧ y ≠ H.nodeMap.symm x → (H.edgeWalkup x).nodeMap y = H.nodeMap y) := by
  refine ⟨?_, ?_, ?_⟩
  · show (Equiv.swap x (H.nodeMap x) * H.nodeMap) x = x
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  · show (Equiv.swap x (H.nodeMap x) * H.nodeMap) (H.nodeMap.symm x) = H.nodeMap x
    rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]
  · intro ⟨hyx, hys⟩
    show (Equiv.swap x (H.nodeMap x) * H.nodeMap) y = H.nodeMap y
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne
        (fun h => hys ((H.nodeMap_inverse_representation y x).mp h.symm))
        (fun h => hyx (H.nodeMap.injective h))]

/-- `hypermap.hl`:1798 `face_map_walkup`。 -/
theorem faceMap_walkup (H : Hypermap α) (x y : α) :
    (H.edgeWalkup x).faceMap x = x ∧
    (H.edgeWalkup x).faceMap (H.faceMap.symm x) = H.faceMap x ∧
    (y ≠ x ∧ y ≠ H.faceMap.symm x → (H.edgeWalkup x).faceMap y = H.faceMap y) := by
  refine ⟨?_, ?_, ?_⟩
  · show (Equiv.swap x (H.faceMap x) * H.faceMap) x = x
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  · show (Equiv.swap x (H.faceMap x) * H.faceMap) (H.faceMap.symm x) = H.faceMap x
    rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]
  · intro ⟨hyx, hys⟩
    show (Equiv.swap x (H.faceMap x) * H.faceMap) y = H.faceMap y
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne
        (fun h => hys ((H.faceMap_inverse_representation y x).mp h.symm))
        (fun h => hyx (H.faceMap.injective h))]

/-- `edgeMap * nodeMap * faceMap` 作用在任意点上恒等（`comp_eq_one` 的应用形式）。 -/
theorem enf_apply (H : Hypermap α) (x : α) : H.edgeMap (H.nodeMap (H.faceMap x)) = x := by
  have h := congrFun (congrArg DFunLike.coe H.comp_eq_one) x
  simpa [Equiv.Perm.mul_apply] using h

/-- `hypermap_cyclic` 第一个轮换的应用形式。 -/
theorem nfe_apply (H : Hypermap α) (x : α) : H.nodeMap (H.faceMap (H.edgeMap x)) = x := by
  have h := congrFun (congrArg DFunLike.coe H.hypermap_cyclic.1) x
  simpa [Equiv.Perm.mul_apply] using h

/-- `hypermap_cyclic` 第二个轮换的应用形式。 -/
theorem fen_apply (H : Hypermap α) (x : α) : H.faceMap (H.edgeMap (H.nodeMap x)) = x := by
  have h := congrFun (congrArg DFunLike.coe H.hypermap_cyclic.2) x
  simpa [Equiv.Perm.mul_apply] using h

/-- `hypermap.hl`:1815 `lemma_edge_degenerate`。 -/
theorem edgeMap_fixed_iff (H : Hypermap α) (x : α) :
    H.edgeMap x = x ↔ H.faceMap x = H.nodeMap.symm x := by
  constructor
  · intro h
    have h1 : H.nodeMap (H.faceMap x) = x := H.edgeMap.injective (by rw [H.enf_apply, h])
    have h2 := (Equiv.symm_apply_apply H.nodeMap (H.faceMap x)).symm
    rw [h1] at h2
    exact h2
  · intro h
    have h1 := H.enf_apply x
    rw [h, Equiv.apply_symm_apply] at h1
    exact h1

/-- `hypermap.hl`:1828 `lemma_node_degenerate`。 -/
theorem nodeMap_fixed_iff (H : Hypermap α) (x : α) :
    H.nodeMap x = x ↔ H.edgeMap x = H.faceMap.symm x := by
  constructor
  · intro h
    have h1 : H.faceMap (H.edgeMap x) = x := H.nodeMap.injective (by rw [H.nfe_apply, h])
    have h2 := (Equiv.symm_apply_apply H.faceMap (H.edgeMap x)).symm
    rw [h1] at h2
    exact h2
  · intro h
    have h1 := H.nfe_apply x
    rw [h, Equiv.apply_symm_apply] at h1
    exact h1

/-- `hypermap.hl`:1841 `lemma_face_degenerate`。 -/
theorem faceMap_fixed_iff (H : Hypermap α) (x : α) :
    H.faceMap x = x ↔ H.nodeMap x = H.edgeMap.symm x := by
  constructor
  · intro h
    have h1 : H.edgeMap (H.nodeMap x) = x := H.faceMap.injective (by rw [H.fen_apply, h])
    have h2 := (Equiv.symm_apply_apply H.edgeMap (H.nodeMap x)).symm
    rw [h1] at h2
    exact h2
  · intro h
    have h1 := H.fen_apply x
    rw [h, Equiv.apply_symm_apply] at h1
    exact h1

/-- `hypermap.hl`:1868 `lemma_inverse_maps_at_nondegenerate_dart`。 -/
theorem inverse_maps_at_nondegenerate_dart (H : Hypermap α) (hx : H.DartNondegenerate x) :
    H.edgeMap.symm x ≠ x ∧ H.nodeMap.symm x ≠ x ∧ H.faceMap.symm x ≠ x :=
  ⟨(Perm_apply_ne_self_iff_symm _ _).mp hx.1,
   (Perm_apply_ne_self_iff_symm _ _).mp hx.2.1,
   (Perm_apply_ne_self_iff_symm _ _).mp hx.2.2⟩

/-- `hypermap.hl`:1872 `aux_permutes_conversion`（`Equiv.Perm` 版本无需 permutes 前提）。 -/
theorem Perm_inv_apply_inv_apply_iff {α : Type*} (f g : Equiv.Perm α) (x y : α) :
    f⁻¹ (g⁻¹ x) = y ↔ g (f y) = x := by
  show f.symm (g.symm x) = y ↔ g (f y) = x
  rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, eq_comm]

/-- `hypermap.hl`:1880 `edge_map_walkup`。
（证明统一走 `Perm_inv_apply_inv_apply_iff` 正规形：`e' z = w ⟺ n' (f' w) = z`。） -/
theorem edgeMap_walkup (H : Hypermap α) (x y : α) :
    (H.edgeWalkup x).edgeMap x = x ∧
    (H.nodeMap x ≠ x ∧ H.edgeMap x ≠ x →
      (H.edgeWalkup x).edgeMap (H.nodeMap x) = H.edgeMap x) ∧
    (H.faceMap⁻¹ x ≠ x ∧ H.edgeMap⁻¹ x ≠ x →
      (H.edgeWalkup x).edgeMap (H.edgeMap⁻¹ x) = H.faceMap⁻¹ x) ∧
    (y ≠ x ∧ y ≠ H.edgeMap⁻¹ x ∧ y ≠ H.nodeMap x →
      (H.edgeWalkup x).edgeMap y = H.edgeMap y) := by
  set n' := Equiv.swap x (H.nodeMap x) * H.nodeMap with hn'
  set f' := Equiv.swap x (H.faceMap x) * H.faceMap with hf'
  have key : ∀ z w : α, (H.edgeWalkup x).edgeMap z = w ↔ n' (f' w) = z := by
    intro z w
    show ((f'⁻¹ * n'⁻¹) z = w) ↔ n' (f' w) = z
    rw [Equiv.Perm.mul_apply, Perm_inv_apply_inv_apply_iff]
  have hNx : n' x = x := (H.nodeMap_walkup x y).1
  have hFx : f' x = x := (H.faceMap_walkup x y).1
  have hNsy : n' (H.nodeMap.symm x) = H.nodeMap x := (H.nodeMap_walkup x y).2.1
  have hFsy : f' (H.faceMap.symm x) = H.faceMap x := (H.faceMap_walkup x y).2.1
  have hN : ∀ z : α, z ≠ x → z ≠ H.nodeMap.symm x → n' z = H.nodeMap z :=
    fun z h1 h2 => (H.nodeMap_walkup x z).2.2 ⟨h1, h2⟩
  have hF : ∀ z : α, z ≠ x → z ≠ H.faceMap.symm x → f' z = H.faceMap z :=
    fun z h1 h2 => (H.faceMap_walkup x z).2.2 ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, hFx, hNx]
  · -- `e' (n x) = e x`，即 `n' (f' (e x)) = n x`：用 `f (e x) = n⁻¹ x`（`nfe_apply`）。
    intro ⟨hn, he⟩
    have hfe : H.faceMap (H.edgeMap x) = H.nodeMap.symm x :=
      ((Equiv.symm_apply_eq H.nodeMap).mpr (H.nfe_apply x).symm).symm
    have hey : H.edgeMap x ≠ H.faceMap.symm x := by
      intro hcon
      apply hn
      have h1 : H.faceMap (H.edgeMap x) = x := by
        rw [hcon]; exact Equiv.apply_symm_apply _ _
      calc H.nodeMap x = H.nodeMap (H.faceMap (H.edgeMap x)) := by rw [h1]
        _ = x := H.nfe_apply x
    rw [key, hF (H.edgeMap x) he hey, hfe, hNsy]
  · -- `e' (e⁻¹ x) = f⁻¹ x`，即 `n' (f' (f⁻¹ x)) = e⁻¹ x`：用 `f' (f⁻¹ x) = f x` 与 `n (f x) = e⁻¹ x`。
    intro ⟨hf, he⟩
    have hfx : H.faceMap x ≠ x := by
      intro hcon
      apply hf
      calc H.faceMap⁻¹ x = H.faceMap⁻¹ (H.faceMap x) := by rw [hcon]
        _ = x := Equiv.symm_apply_apply _ _
    have hfx2 : H.faceMap x ≠ H.nodeMap.symm x := by
      intro hcon
      apply he
      have h1 : H.edgeMap x = x := by
        have h2 := H.enf_apply x
        rw [hcon, Equiv.apply_symm_apply] at h2
        exact h2
      calc H.edgeMap⁻¹ x = H.edgeMap⁻¹ (H.edgeMap x) := by rw [h1]
        _ = x := Equiv.symm_apply_apply _ _
    have hFx' : f' (H.faceMap⁻¹ x) = H.faceMap x := hFsy
    rw [key, hFx', hN (H.faceMap x) hfx hfx2]
    show H.nodeMap (H.faceMap x) = H.edgeMap⁻¹ x
    rw [H.inverse_hypermap_maps.1, Equiv.Perm.mul_apply]
  · -- `e' y = e y`，即 `n' (f' (e y)) = y`：两端都用第三分量求值。
    intro ⟨hy1, hy2, hy3⟩
    have hey1 : H.edgeMap y ≠ x := by
      intro hcon
      exact hy2 ((Equiv.symm_apply_eq H.edgeMap).mpr hcon.symm).symm
    have hey2 : H.edgeMap y ≠ H.faceMap.symm x := by
      intro hcon
      apply hy3
      have h1 : H.faceMap (H.edgeMap y) = x := by
        rw [hcon]; exact Equiv.apply_symm_apply _ _
      calc y = H.nodeMap (H.faceMap (H.edgeMap y)) := (H.nfe_apply y).symm
        _ = H.nodeMap x := by rw [h1]
    have hfey1 : H.faceMap (H.edgeMap y) ≠ x := by
      intro hcon
      exact hy3 (by rw [← H.nfe_apply y, hcon])
    have hfey2 : H.faceMap (H.edgeMap y) ≠ H.nodeMap.symm x := by
      intro hcon
      apply hy1
      have h1 : H.nodeMap (H.faceMap (H.edgeMap y)) = x := by
        rw [hcon]; exact Equiv.apply_symm_apply _ _
      rw [H.nfe_apply] at h1
      exact h1
    rw [key, hF (H.edgeMap y) hey1 hey2, hN (H.faceMap (H.edgeMap y)) hfey1 hfey2]
    exact H.nfe_apply y

end Hypermap

/-! ## 轨道的精细结构（`hypermap.hl`:1982–2097） -/

section InjOrbit

variable {α : Type*} {p : Equiv.Perm α} {s : Finset α} {x y : α}

/-- `hypermap.hl`:1982 `power_sequence`。 -/
def powerSeq (p : Equiv.Perm α) (x : α) : ℕ → α := fun i => (p ^ i) x

/-- `hypermap.hl`:1984 `inj_orbit`（不经 `is_inj_list`，直接递归定义）。 -/
def injOrbit (p : Equiv.Perm α) (x : α) : ℕ → Prop
  | 0 => True
  | n + 1 => injOrbit p x n ∧ (∀ j ≤ n, (p ^ (n + 1)) x ≠ (p ^ j) x)

theorem injOrbit_succ (p : Equiv.Perm α) (x : α) (n : ℕ) :
    injOrbit p x (n + 1) ↔ injOrbit p x n ∧ (∀ j ≤ n, (p ^ (n + 1)) x ≠ (p ^ j) x) := Iff.rfl

/-- `hypermap.hl`:1995 `lemma_def_inj_orbit`。 -/
theorem injOrbit_iff (p : Equiv.Perm α) (x : α) (n : ℕ) :
    injOrbit p x n ↔ ∀ i j : ℕ, i ≤ n → j < i → (p ^ i) x ≠ (p ^ j) x := by
  constructor
  · intro h
    induction n with
    | zero => intro i j hi hj; omega
    | succ k ih =>
      rw [injOrbit_succ] at h
      intro i j hi hj
      rcases (by omega : i ≤ k ∨ i = k + 1) with hik | rfl
      · exact ih h.1 i j hik hj
      · exact h.2 j (by omega)
  · intro h
    induction n with
    | zero => trivial
    | succ k ih =>
      rw [injOrbit_succ]
      refine ⟨ih (fun i j hi hj => h i j (hi.trans k.le_succ) hj), fun j hj => ?_⟩
      exact h (k + 1) j (by omega) (by omega)

/-- `hypermap.hl`:2000 `lemma_inj_orbit`。 -/
theorem injOrbit_iff_pairwise (p : Equiv.Perm α) (x : α) (n : ℕ) :
    injOrbit p x n ↔ ∀ i j : ℕ, i ≤ n → j ≤ n → (p ^ i) x = (p ^ j) x → i = j := by
  rw [injOrbit_iff]
  constructor
  · intro h i j hi hj heq
    rcases lt_trichotomy i j with hlt | heq' | hgt
    · exact absurd heq.symm (h j i hj hlt)
    · exact heq'
    · exact absurd heq (h i j hi hgt)
  · intro h i j hi hj hcon
    have := h i j hi (hj.le.trans hi) hcon
    omega

/-- `hypermap.hl`:820 `elim_power_function`。 -/
theorem Perm.pow_apply_eq_pow_apply_cancel (p : Equiv.Perm α) {m k : ℕ} {x : α}
    (h : (p ^ (m + k)) x = (p ^ m) x) : (p ^ k) x = x := by
  rw [pow_add, Equiv.Perm.mul_apply] at h
  exact (p ^ m).injective h

/-- `hypermap.hl`:2003 `inj_orbit_step`。 -/
theorem PermutesOn.injOrbit_step (_hp : PermutesOn p s) (h : injOrbit p x n)
    (hne : (p ^ (n + 1)) x ≠ x) : injOrbit p x (n + 1) := by
  rw [injOrbit_succ]
  refine ⟨h, fun j hj hcon => ?_⟩
  by_cases hj0 : j = 0
  · subst hj0
    exact hne (by simpa using hcon)
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, j = d + 1 := ⟨j - 1, by omega⟩
    have hsplit : n + 1 = (d + 1) + (n - d) := by omega
    have hfix : (p ^ (n - d)) x = x := by
      apply Perm.pow_apply_eq_pow_apply_cancel (m := d + 1) (k := n - d)
      rw [← hsplit]; exact hcon
    rw [injOrbit_iff] at h
    exact h (n - d) 0 (by omega) (by omega) hfix

/-- `hypermap.hl`:2022 `lemma_subset_orbit`。 -/
theorem image_range_le_subset_orbitMap (p : Equiv.Perm α) (x : α) (n : ℕ) :
    (fun i => (p ^ i) x) '' ↑(Finset.range (n + 1)) ⊆ orbitMap p x := by
  rintro y ⟨i, -, rfl⟩
  exact pow_apply_mem_orbitMap p i x

/-- `injOrbit` 时前 `n + 1` 个幂两两不同（`hypermap.hl`:585 `lemma_size_list` 的轨道版）。 -/
theorem ncard_image_range_le_of_injOrbit (p : Equiv.Perm α) (x : α) {n : ℕ}
    (h : injOrbit p x n) :
    ((fun i => (p ^ i) x) '' ↑(Finset.range (n + 1))).ncard = n + 1 := by
  rw [injOrbit_iff_pairwise] at h
  have hinj : Set.InjOn (fun i => (p ^ i) x) ↑(Finset.range (n + 1)) := by
    intro i hi j hj hij
    have hi' : i < n + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' : j < n + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    exact h i j (by omega) (by omega) hij
  rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]

/-- `hypermap.hl`:2027 `lemma_segment_orbit`。 -/
theorem PermutesOn.injOrbit_of_lt_ncard (hp : PermutesOn p s) :
    ∀ {m : ℕ}, m < (orbitMap p x).ncard → injOrbit p x m := by
  intro m
  induction m with
  | zero => intro _; trivial
  | succ k ih =>
    intro hkm
    have h1 : injOrbit p x k := ih (by omega)
    apply hp.injOrbit_step h1
    intro hcon
    have hle := card_orbit_le p (by omega : k + 1 ≠ 0) hcon
    omega

/-- `hypermap.hl`:2039 `lemma_cycle_orbit`。 -/
theorem PermutesOn.pow_ncard_orbitMap_apply_self (hp : PermutesOn p s) (x : α) :
    (p ^ ((orbitMap p x).ncard)) x = x := by
  have hfin := orbitMap_finite hp x
  have hpos : 0 < (orbitMap p x).ncard := by
    rw [Set.ncard_pos hfin]; exact ⟨x, mem_orbitMap_self p x⟩
  set c := (orbitMap p x).ncard with hc
  by_contra hne
  have hm : injOrbit p x (c - 1) := hp.injOrbit_of_lt_ncard (by omega)
  have hstep : injOrbit p x c := by
    have h := hp.injOrbit_step hm (by rwa [(by omega : c - 1 + 1 = c)])
    rwa [(by omega : c - 1 + 1 = c)] at h
  have hcard := ncard_image_range_le_of_injOrbit p x hstep
  have hsub := image_range_le_subset_orbitMap p x c
  have hle := Set.ncard_le_ncard hsub hfin
  rw [hcard] at hle
  omega

/-- `hypermap.hl`:2064 `lemma_index_on_orbit`。 -/
theorem PermutesOn.exists_lt_ncard_pow_apply (hp : PermutesOn p s)
    (hy : y ∈ orbitMap p x) : ∃ n : ℕ, n < (orbitMap p x).ncard ∧ y = (p ^ n) x := by
  have hfin := orbitMap_finite hp x
  have hpos : 0 < (orbitMap p x).ncard := by
    rw [Set.ncard_pos hfin]; exact ⟨x, mem_orbitMap_self p x⟩
  rw [orbit_cyclic p hpos.ne' (hp.pow_ncard_orbitMap_apply_self x)] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact ⟨n, Finset.mem_range.mp hn, rfl⟩

/-- `hypermap.hl`:2076 `lemma_congruence_on_orbit`。 -/
theorem PermutesOn.exists_mul_ncard_add_of_pow_eq (hp : PermutesOn p s) {n m : ℕ}
    (hn : n < (orbitMap p x).ncard) (h : (p ^ n) x = (p ^ m) x) :
    ∃ q : ℕ, m = q * (orbitMap p x).ncard + n := by
  have hfin := orbitMap_finite hp x
  have hpos : 0 < (orbitMap p x).ncard := by
    rw [Set.ncard_pos hfin]; exact ⟨x, mem_orbitMap_self p x⟩
  set c := (orbitMap p x).ncard with hc
  obtain ⟨q, r, hqr, hr⟩ : ∃ q r : ℕ, m = q * c + r ∧ r < c :=
    ⟨m / c, m % c, by rw [Nat.mul_comm]; exact (Nat.div_add_mod m c).symm,
      Nat.mod_lt m hpos⟩
  have hcycle : ((p ^ c) ^ q) x = x := pow_fix_pow p (hp.pow_ncard_orbitMap_apply_self x) q
  have heq : (p ^ r) x = (p ^ n) x := by
    rw [h]
    have hm : m = r + q * c := by rw [hqr, Nat.add_comm]
    rw [hm, pow_add, Equiv.Perm.mul_apply, pow_mul', hcycle]
  have hinj : injOrbit p x (c - 1) := hp.injOrbit_of_lt_ncard (by omega)
  rw [injOrbit_iff_pairwise] at hinj
  have hrn : r = n := hinj r n (by omega) (by omega) heq
  exact ⟨q, by rw [hqr, hrn]⟩

/-- `hypermap.hl`:2115 `INVERSE_EVALUATION`（`⁻¹` 形式）。 -/
theorem PermutesOn.exists_pow_inv_apply (hp : PermutesOn p s) (x : α) :
    ∃ j : ℕ, p⁻¹ x = (p ^ j) x := by
  obtain ⟨j, hj⟩ := hp.exists_pow_eq_inv
  exact ⟨j, by rw [← hj]⟩

/-- `hypermap.hl`:2115 `INVERSE_EVALUATION`（`symm` 形式）。 -/
theorem PermutesOn.exists_pow_symm_apply (hp : PermutesOn p s) (x : α) :
    ∃ j : ℕ, p.symm x = (p ^ j) x := hp.exists_pow_inv_apply x

/-- `hypermap.hl`:2152 `lemma_orbit_power`。 -/
theorem PermutesOn.orbitMap_pow_apply (hp : PermutesOn p s) (n : ℕ) (x : α) :
    orbitMap p x = orbitMap p ((p ^ n) x) :=
  (orbitMap_eq_of_mem hp (pow_apply_mem_orbitMap p n x)).symm

/-- `hypermap.hl`:2159 `lemma_inverse_in_orbit`。 -/
theorem PermutesOn.symm_apply_mem_orbitMap (hp : PermutesOn p s) (x : α) :
    p.symm x ∈ orbitMap p x := by
  obtain ⟨j, hj⟩ := hp.exists_pow_symm_apply x
  rw [hj]
  exact pow_apply_mem_orbitMap p j x

/-- `hypermap.hl`:2258 `in_orbit_map1`。 -/
theorem apply_mem_orbitMap (f : Equiv.Perm α) (x : α) : f x ∈ orbitMap f x :=
  pow_apply_mem_orbitMap f 1 x

/-- `hypermap.hl`:2263 `lemma_orbit_eq`。 -/
theorem orbitMap_eq_of_pow_apply_eq (p q : Equiv.Perm α) (x : α)
    (h : ∀ n : ℕ, (p ^ n) x = (q ^ n) x) : orbitMap p x = orbitMap q x := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, (h n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, h n⟩

/-- `hypermap.hl`:2275 `lemma_not_in_orbit_powers`。 -/
theorem PermutesOn.pow_apply_ne_pow_apply_of_not_mem (hp : PermutesOn p s)
    (hy : y ∉ orbitMap p x) (n m : ℕ) : (p ^ n) y ≠ (p ^ m) x := by
  intro hcon
  apply hy
  have h1 : (p ^ m) x ∈ orbitMap p y := by
    have h2 : (p ^ n) y ∈ orbitMap p ((p ^ n) y) := mem_orbitMap_self _ _
    rw [← hp.orbitMap_pow_apply n y] at h2
    rwa [hcon] at h2
  have h3 : orbitMap p y = orbitMap p x :=
    (orbitMap_eq_of_mem hp h1).symm.trans (hp.orbitMap_pow_apply m x).symm
  exact h3.symm ▸ mem_orbitMap_self p y

end InjOrbit

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `hypermap.hl`:2103 `is_edge_merge`。 -/
def IsEdgeMerge (H : Hypermap α) (x : α) : Prop :=
  H.DartNondegenerate x ∧ H.nodeMap x ∉ H.edge x

/-- `hypermap.hl`:2105 `is_node_merge`。 -/
def IsNodeMerge (H : Hypermap α) (x : α) : Prop :=
  H.DartNondegenerate x ∧ H.faceMap x ∉ H.node x

/-- `hypermap.hl`:2107 `is_face_merge`。 -/
def IsFaceMerge (H : Hypermap α) (x : α) : Prop :=
  H.DartNondegenerate x ∧ H.edgeMap x ∉ H.face x

/-- `hypermap.hl`:2109 `is_edge_split`。 -/
def IsEdgeSplit (H : Hypermap α) (x : α) : Prop :=
  H.DartNondegenerate x ∧ H.nodeMap x ∈ H.edge x

/-- `hypermap.hl`:2111 `is_node_split`。 -/
def IsNodeSplit (H : Hypermap α) (x : α) : Prop :=
  H.DartNondegenerate x ∧ H.faceMap x ∈ H.node x

/-- `hypermap.hl`:2113 `is_face_split`。 -/
def IsFaceSplit (H : Hypermap α) (x : α) : Prop :=
  H.DartNondegenerate x ∧ H.edgeMap x ∈ H.face x

/-- `hypermap.hl`:2138 `lemma_edge_identity`。 -/
theorem edge_eq_of_mem (H : Hypermap α) (hy : y ∈ H.edge x) : H.edge x = H.edge y :=
  (orbitMap_eq_of_mem H.edgeMap_permutes hy).symm

/-- `hypermap.hl`:2141 `lemma_node_identity`。 -/
theorem node_eq_of_mem (H : Hypermap α) (hy : y ∈ H.node x) : H.node x = H.node y :=
  (orbitMap_eq_of_mem H.nodeMap_permutes hy).symm

/-- `hypermap.hl`:2144 `lemma_face_identity`。 -/
theorem face_eq_of_mem (H : Hypermap α) (hy : y ∈ H.face x) : H.face x = H.face y :=
  (orbitMap_eq_of_mem H.faceMap_permutes hy).symm

/-- `hypermap.hl`:2170 `planar_index`（HOL 用 `&` 嵌入 ℝ；我们用 `ℤ`，
对计数论证等价且可用 `omega` 收尾）。 -/
noncomputable def planarIndex (H : Hypermap α) : ℤ :=
  H.numberOfEdges + H.numberOfNodes + H.numberOfFaces - H.darts.card -
    2 * H.numberOfComponents

/-- `hypermap.hl`:2175 `lemma_planar_hypermap`。 -/
theorem planar_iff_planarIndex_eq_zero (H : Hypermap α) :
    H.Planar ↔ H.planarIndex = 0 := by
  unfold Planar planarIndex
  omega

/-- `hypermap.hl`:2179 `lemma_null_hypermap_planar_index`。 -/
theorem planarIndex_eq_zero_of_darts_card_eq_zero (H : Hypermap α)
    (h : H.darts.card = 0) : H.planarIndex = 0 := by
  have hd : H.darts = ∅ := Finset.card_eq_zero.mp h
  have ho : ∀ f : Equiv.Perm α, setOfOrbits H.darts f = ∅ := fun f => by
    ext u; simp [setOfOrbits, hd]
  have hc : H.setPartComponents H.darts = ∅ := by
    ext u; simp [setPartComponents, hd]
  simp [planarIndex, numberOfEdges, numberOfNodes, numberOfFaces, numberOfComponents,
    edgeSet, nodeSet, faceSet, setOfComponents, ho, hc, h]

/-- `hypermap.hl`:2190 `lemma_shift_component_invariant`。 -/
theorem setOfComponents_shift (H : Hypermap α) :
    H.setOfComponents = H.shift.setOfComponents := by
  have hstep : ∀ x y : α, H.goOneStep x y ↔ H.shift.goOneStep x y := by
    intro x y
    show (_ ∨ _ ∨ _) ↔ (_ ∨ _ ∨ _)
    tauto
  have hpath : ∀ (p : ℕ → α) (n : ℕ), H.isPath p n ↔ H.shift.isPath p n := by
    intro p n
    rw [H.isPath_iff, H.shift.isPath_iff]
    exact forall_congr' fun i => forall_congr' fun _ => hstep _ _
  have hcomp : ∀ x y : α, H.isInComponent x y ↔ H.shift.isInComponent x y := by
    intro x y
    show (∃ p : ℕ → α, ∃ n : ℕ, p 0 = x ∧ p n = y ∧ H.isPath p n) ↔
      ∃ p : ℕ → α, ∃ n : ℕ, p 0 = x ∧ p n = y ∧ H.shift.isPath p n
    exact exists_congr fun p => exists_congr fun n =>
      and_congr (Iff.refl _) (and_congr (Iff.refl _) (hpath p n))
  have hcc : ∀ x : α, H.combComponent x = H.shift.combComponent x := by
    intro x
    ext y
    exact hcomp x y
  show H.setPartComponents H.darts = H.shift.setPartComponents H.shift.darts
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hcc x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hcc x⟩

/-- `hypermap.hl`:2251 `lemma_planar_invariant_shift`。 -/
theorem planarIndex_shift (H : Hypermap α) : H.planarIndex = H.shift.planarIndex := by
  have hE : H.shift.numberOfEdges = H.numberOfNodes := rfl
  have hN : H.shift.numberOfNodes = H.numberOfFaces := rfl
  have hF : H.shift.numberOfFaces = H.numberOfEdges := rfl
  have hD : H.shift.darts.card = H.darts.card := rfl
  have hC := H.setOfComponents_shift
  unfold planarIndex numberOfComponents
  rw [hE, hN, hF, hD, hC]
  omega

/-- `hypermap.hl`:2286/2397 `lemma_walkup_nodes`/`lemma_walkup_faces` 的统一形式。
`p` 取 `nodeMap`（对应 walkup 后 `p' = (edgeWalkup x).nodeMap`）或 `faceMap`。 -/
theorem walkup_orbits_delete (H : Hypermap α) {x : α} (_hx : x ∈ H.darts)
    {p p' : Equiv.Perm α} (hp : PermutesOn p H.darts)
    (heval : p' x = x ∧ p' (p.symm x) = p x ∧
      ∀ y : α, y ≠ x → y ≠ p.symm x → p' y = p y)
    (hp' : PermutesOn p' (H.darts.erase x)) :
    setOfOrbits H.darts p \ {orbitMap p x} =
      setOfOrbits (H.darts.erase x) p' \ {orbitMap p' (p.symm x)} := by
  obtain ⟨j, hj⟩ := hp.exists_pow_symm_apply x
  ext u
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hne⟩
    have hyx : y ∉ orbitMap p x := fun hcon => hne (orbitMap_eq_of_mem hp hcon)
    have hyx2 : y ≠ x := fun h => hne (by rw [h])
    have hpow : ∀ m : ℕ, (p ^ m) y = (p' ^ m) y := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
        have h1 : (p' ^ m) y ≠ x := by
          rw [← ih]
          exact hp.pow_apply_ne_pow_apply_of_not_mem hyx m 0
        have h2 : (p' ^ m) y ≠ p.symm x := by
          rw [← ih, hj]
          exact hp.pow_apply_ne_pow_apply_of_not_mem hyx m j
        rw [← heval.2.2 _ h1 h2, pow_succ', Equiv.Perm.mul_apply]
    have hu : orbitMap p y = orbitMap p' y := orbitMap_eq_of_pow_apply_eq p p' y hpow
    refine ⟨⟨y, Finset.mem_erase.mpr ⟨hyx2, hy⟩, hu.symm⟩, ?_⟩
    intro hcon
    have hmem : p.symm x ∈ orbitMap p y := by
      have h1 : p.symm x ∈ orbitMap p' (p.symm x) := mem_orbitMap_self _ _
      rwa [← hcon] at h1
    rw [hj] at hmem
    have h3 : orbitMap p x = orbitMap p y :=
      (hp.orbitMap_pow_apply j x).trans (orbitMap_eq_of_mem hp hmem)
    exact hyx (h3.symm ▸ mem_orbitMap_self p y)
  · rintro ⟨⟨y, hy, rfl⟩, hne⟩
    rw [Finset.mem_erase] at hy
    obtain ⟨hyx2, hyD⟩ := hy
    have hpow : ∀ m : ℕ, (p ^ m) y = (p' ^ m) y := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
        have h1 : (p' ^ m) y ≠ x := by
          have hsub : (p' ^ m) y ∈ H.darts.erase x :=
            hp'.pow_apply_mem m (Finset.mem_erase.mpr ⟨hyx2, hyD⟩)
          exact (Finset.mem_erase.mp hsub).1
        have h2 : (p' ^ m) y ≠ p.symm x := by
          intro hcon
          apply hne
          have hmem : p.symm x ∈ orbitMap p' y := hcon ▸ pow_apply_mem_orbitMap p' m y
          exact (orbitMap_eq_of_mem hp' hmem).symm
        rw [← heval.2.2 _ h1 h2, pow_succ', Equiv.Perm.mul_apply]
    refine ⟨⟨y, hyD, orbitMap_eq_of_pow_apply_eq p p' y hpow⟩, ?_⟩
    intro hcon
    apply hne
    have hmem : p.symm x ∈ orbitMap p x := hj ▸ pow_apply_mem_orbitMap p j x
    rw [← hcon] at hmem
    exact (orbitMap_eq_of_mem hp' hmem).symm

/-- `hypermap.hl`:2286 `lemma_walkup_nodes`。 -/
theorem nodeSet_walkup (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.nodeSet \ {H.node x} =
      (H.edgeWalkup x).nodeSet \ {(H.edgeWalkup x).node (H.nodeMap.symm x)} :=
  H.walkup_orbits_delete hx H.nodeMap_permutes
    ⟨(H.nodeMap_walkup x x).1, (H.nodeMap_walkup x x).2.1,
      fun y h1 h2 => (H.nodeMap_walkup x y).2.2 ⟨h1, h2⟩⟩
    (H.edgeWalkup x).nodeMap_permutes

/-- `hypermap.hl`:2397 `lemma_walkup_faces`。 -/
theorem faceSet_walkup (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.faceSet \ {H.face x} =
      (H.edgeWalkup x).faceSet \ {(H.edgeWalkup x).face (H.faceMap.symm x)} :=
  H.walkup_orbits_delete hx H.faceMap_permutes
    ⟨(H.faceMap_walkup x x).1, (H.faceMap_walkup x x).2.1,
      fun y h1 h2 => (H.faceMap_walkup x y).2.2 ⟨h1, h2⟩⟩
    (H.edgeWalkup x).faceMap_permutes

/-- `hypermap.hl`:2508 `lemma_walkup_first_edge_eq`。 -/
theorem walkup_first_edge_eq (H : Hypermap α) {x y : α}
    (_hx : x ∈ H.darts) (h2 : x ∉ H.edge y) (h4 : H.nodeMap x ∉ H.edge y) :
    H.edge y = (H.edgeWalkup x).edge y ∧ H.edgeMap⁻¹ x ∉ H.edge y := by
  have hpow : ∀ m : ℕ, (H.edgeMap ^ m) y = ((H.edgeWalkup x).edgeMap ^ m) y := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      have h1 : ((H.edgeWalkup x).edgeMap ^ m) y ≠ x := by
        rw [← ih]
        intro hcon
        exact h2 ⟨m, hcon⟩
      have h2' : ((H.edgeWalkup x).edgeMap ^ m) y ≠ H.edgeMap⁻¹ x := by
        rw [← ih]
        intro hcon
        apply h2
        have h3 : (H.edgeMap ^ (m + 1)) y = x := by
          rw [pow_succ', Equiv.Perm.mul_apply, hcon]
          show H.edgeMap (H.edgeMap.symm x) = x
          exact Equiv.apply_symm_apply _ _
        exact ⟨m + 1, h3⟩
      have h3 : ((H.edgeWalkup x).edgeMap ^ m) y ≠ H.nodeMap x := by
        rw [← ih]
        intro hcon
        exact h4 ⟨m, hcon⟩
      rw [← (H.edgeMap_walkup x _).2.2.2 ⟨h1, h2', h3⟩, pow_succ', Equiv.Perm.mul_apply]
  have horbit : H.edge y = (H.edgeWalkup x).edge y :=
    orbitMap_eq_of_pow_apply_eq H.edgeMap (H.edgeWalkup x).edgeMap y hpow
  refine ⟨horbit, ?_⟩
  intro hcon
  apply h2
  obtain ⟨j, hj⟩ := H.edgeMap_permutes.exists_pow_symm_apply x
  have h1 : H.edge y = H.edge (H.edgeMap.symm x) := H.edge_eq_of_mem hcon
  have h2' : H.edge x = H.edge (H.edgeMap.symm x) := by
    rw [hj]
    exact H.edgeMap_permutes.orbitMap_pow_apply j x
  exact (h2'.trans h1.symm) ▸ H.mem_edge_self x

/-- `hypermap.hl`:2559 `lemma_walkup_second_edge_eq`。 -/
theorem walkup_second_edge_eq (H : Hypermap α) {x y : α}
    (_hx : x ∈ H.darts) (hy : y ∈ H.darts) (hyx : y ≠ x)
    (h4 : H.nodeMap x ∉ (H.edgeWalkup x).edge y)
    (h5 : H.edgeMap⁻¹ x ∉ (H.edgeWalkup x).edge y) :
    H.edge y = (H.edgeWalkup x).edge y ∧ x ∉ H.edge y ∧ H.nodeMap x ∉ H.edge y := by
  have hyE : y ∈ H.darts.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
  have hpow : ∀ m : ℕ, (H.edgeMap ^ m) y = ((H.edgeWalkup x).edgeMap ^ m) y := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      have h0 : ((H.edgeWalkup x).edgeMap ^ m) y ≠ x := by
        have hsub := (H.edgeWalkup x).edgeMap_permutes.pow_apply_mem m hyE
        exact (Finset.mem_erase.mp hsub).1
      have h2' : ((H.edgeWalkup x).edgeMap ^ m) y ≠ H.edgeMap⁻¹ x := by
        intro hcon
        apply h5
        rw [← hcon]
        exact pow_apply_mem_orbitMap _ _ _
      have h3 : ((H.edgeWalkup x).edgeMap ^ m) y ≠ H.nodeMap x := by
        intro hcon
        apply h4
        rw [← hcon]
        exact pow_apply_mem_orbitMap _ _ _
      rw [← (H.edgeMap_walkup x _).2.2.2 ⟨h0, h2', h3⟩, pow_succ', Equiv.Perm.mul_apply]
  have horbit : H.edge y = (H.edgeWalkup x).edge y :=
    orbitMap_eq_of_pow_apply_eq H.edgeMap (H.edgeWalkup x).edgeMap y hpow
  refine ⟨horbit, ?_, ?_⟩
  · intro hcon
    rw [horbit] at hcon
    exact (Finset.mem_erase.mp ((H.edgeWalkup x).edge_subset_darts hyE hcon)).1 rfl
  · rw [horbit]; exact h4

/-- `hypermap.hl`:2612 `lemma_walkup_edges`。 -/
theorem edgeSet_walkup (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.edgeSet \ {H.edge x, H.edge (H.nodeMap x)} =
      (H.edgeWalkup x).edgeSet \
        {(H.edgeWalkup x).edge (H.nodeMap x), (H.edgeWalkup x).edge (H.edgeMap⁻¹ x)} := by
  ext u
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h4, h5⟩
    have h6 : x ∉ H.edge y := fun hcon => h4 (H.edge_eq_of_mem hcon)
    have h7 : H.nodeMap x ∉ H.edge y := fun hcon => h5 (H.edge_eq_of_mem hcon)
    obtain ⟨horbit, h8⟩ := H.walkup_first_edge_eq hx h6 h7
    have hyx : y ≠ x := fun h => h4 (by rw [h]; rfl)
    refine ⟨⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩, horbit.symm⟩, ?_, ?_⟩
    · intro hcon
      apply h7
      show H.nodeMap x ∈ orbitMap H.edgeMap y
      exact hcon.symm ▸ (H.edgeWalkup x).mem_edge_self _
    · intro hcon
      apply h8
      show H.edgeMap⁻¹ x ∈ orbitMap H.edgeMap y
      exact hcon.symm ▸ (H.edgeWalkup x).mem_edge_self _
  · rintro ⟨⟨y, hy, rfl⟩, h4, h5⟩
    have hy' : y ∈ H.darts.erase x := hy
    rw [Finset.mem_erase] at hy'
    obtain ⟨hyx, hyD⟩ := hy'
    have h6 : H.nodeMap x ∉ (H.edgeWalkup x).edge y := fun hcon =>
      h4 ((H.edgeWalkup x).edge_eq_of_mem hcon)
    have h7 : H.edgeMap⁻¹ x ∉ (H.edgeWalkup x).edge y := fun hcon =>
      h5 ((H.edgeWalkup x).edge_eq_of_mem hcon)
    obtain ⟨horbit, h8, h9⟩ := H.walkup_second_edge_eq hx hyD hyx h6 h7
    refine ⟨⟨y, hyD, horbit⟩, ?_, ?_⟩
    · intro hcon
      apply h8
      rw [horbit]
      show x ∈ orbitMap (H.edgeWalkup x).edgeMap y
      rw [hcon]
      exact H.mem_edge_self x
    · intro hcon
      apply h9
      rw [horbit]
      show H.nodeMap x ∈ orbitMap (H.edgeWalkup x).edgeMap y
      rw [hcon]
      exact H.mem_edge_self _

/-- `hypermap.hl`:2708 `in_set_of_orbits`。 -/
theorem PermutesOn.mem_iff_orbitMap_mem_setOfOrbits {α : Type*} {p : Equiv.Perm α} {s : Finset α}
    (hp : PermutesOn p s) (x : α) : x ∈ s ↔ orbitMap p x ∈ setOfOrbits s p := by
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, h⟩
    have hsub := orbitMap_subset_of_permutesOn hp hy
    rw [h] at hsub
    exact hsub (mem_orbitMap_self p x)

/-- `hypermap.hl`:2721 `lemma_in_hypermap_orbits`。 -/
theorem mem_darts_iff (H : Hypermap α) (x : α) :
    (x ∈ H.darts ↔ H.edge x ∈ H.edgeSet) ∧ (x ∈ H.darts ↔ H.node x ∈ H.nodeSet) ∧
      (x ∈ H.darts ↔ H.face x ∈ H.faceSet) :=
  ⟨PermutesOn.mem_iff_orbitMap_mem_setOfOrbits H.edgeMap_permutes x,
   PermutesOn.mem_iff_orbitMap_mem_setOfOrbits H.nodeMap_permutes x,
   PermutesOn.mem_iff_orbitMap_mem_setOfOrbits H.faceMap_permutes x⟩

/-- `hypermap.hl`:2725 `lemma_in_edge_set`。 -/
theorem mem_darts_iff_edge_mem (H : Hypermap α) (x : α) :
    x ∈ H.darts ↔ H.edge x ∈ H.edgeSet := (H.mem_darts_iff x).1

/-- `hypermap.hl`:2726 `lemma_in_node_set`。 -/
theorem mem_darts_iff_node_mem (H : Hypermap α) (x : α) :
    x ∈ H.darts ↔ H.node x ∈ H.nodeSet := (H.mem_darts_iff x).2.1

/-- `hypermap.hl`:2727 `lemma_in_face_set`。 -/
theorem mem_darts_iff_face_mem (H : Hypermap α) (x : α) :
    x ∈ H.darts ↔ H.face x ∈ H.faceSet := (H.mem_darts_iff x).2.2

/-- `hypermap.hl`:2729 `lemma_edge_representation`。 -/
theorem edge_representation (H : Hypermap α) {u : Set α} (hu : u ∈ H.edgeSet) :
    ∃ x ∈ H.darts, u = H.edge x := hu.imp fun _ h => ⟨h.1, h.2.symm⟩

/-- `hypermap.hl`:2733 `lemma_node_representation`。 -/
theorem node_representation (H : Hypermap α) {u : Set α} (hu : u ∈ H.nodeSet) :
    ∃ x ∈ H.darts, u = H.node x := hu.imp fun _ h => ⟨h.1, h.2.symm⟩

/-- `hypermap.hl`:2737 `lemma_face_representation`。 -/
theorem face_representation (H : Hypermap α) {u : Set α} (hu : u ∈ H.faceSet) :
    ∃ x ∈ H.darts, u = H.face x := hu.imp fun _ h => ⟨h.1, h.2.symm⟩

/-- `hypermap.hl`:3029 `lemma_powers_in_component`。 -/
theorem powers_in_component (H : Hypermap α) (x : α) (j : ℕ) :
    (H.edgeMap ^ j) x ∈ H.combComponent x ∧ (H.nodeMap ^ j) x ∈ H.combComponent x ∧
      (H.faceMap ^ j) x ∈ H.combComponent x :=
  ⟨⟨H.edgePath x, j, H.edgePath_zero x, rfl, H.isPath_edgePath x j⟩,
   ⟨H.nodePath x, j, H.nodePath_zero x, rfl, H.isPath_nodePath x j⟩,
   ⟨H.facePath x, j, H.facePath_zero x, rfl, H.isPath_facePath x j⟩⟩

/-- `hypermap.hl`:3044 `lemma_inverses_in_component`。 -/
theorem inverses_in_component (H : Hypermap α) (x : α) :
    H.edgeMap.symm x ∈ H.combComponent x ∧ H.nodeMap.symm x ∈ H.combComponent x ∧
      H.faceMap.symm x ∈ H.combComponent x := by
  obtain ⟨je, hje⟩ := H.edgeMap_permutes.exists_pow_symm_apply x
  obtain ⟨jn, hjn⟩ := H.nodeMap_permutes.exists_pow_symm_apply x
  obtain ⟨jf, hjf⟩ := H.faceMap_permutes.exists_pow_symm_apply x
  refine ⟨?_, ?_, ?_⟩
  · rw [hje]; exact (H.powers_in_component x je).1
  · rw [hjn]; exact (H.powers_in_component x jn).2.1
  · rw [hjf]; exact (H.powers_in_component x jf).2.2

/-- `hypermap.hl`:3060 `lemma_node_subset_component` 的 edge 版（HOL 未单列，对称补充）。 -/
theorem edge_subset_component (H : Hypermap α) (x : α) :
    H.edge x ⊆ H.combComponent x := by
  rintro y ⟨j, rfl⟩
  exact (H.powers_in_component x j).1

/-- `hypermap.hl`:3060 `lemma_node_subset_component`。 -/
theorem node_subset_component (H : Hypermap α) (x : α) :
    H.node x ⊆ H.combComponent x := by
  rintro y ⟨j, rfl⟩
  exact (H.powers_in_component x j).2.1

/-- `hypermap.hl`:3068 `lemma_face_subset_component`。 -/
theorem face_subset_component (H : Hypermap α) (x : α) :
    H.face x ⊆ H.combComponent x := by
  rintro y ⟨j, rfl⟩
  exact (H.powers_in_component x j).2.2

/-- `hypermap.hl`:3076 `lemma_component_identity`。 -/
theorem combComponent_eq_of_mem (H : Hypermap α) (h : y ∈ H.combComponent x) :
    H.combComponent x = H.combComponent y := by
  rcases H.partition_components x y with h1 | h1
  · exact h1
  · exfalso
    have h2 : y ∈ H.combComponent x ∩ H.combComponent y :=
      ⟨h, H.mem_combComponent_self y⟩
    rw [h1] at h2
    exact h2

/-- 一步扩展：`isInComponent` 与 `goOneStep` 的复合。 -/
theorem isInComponent_trans_step (H : Hypermap α) (h : H.isInComponent x y)
    (hs : H.goOneStep y z) : H.isInComponent x z := by
  obtain ⟨p, n, hp0, hpn, hp⟩ := h
  have hq : H.isPath (fun i => if i = 0 then y else z) 1 := by
    rw [H.isPath_succ]
    exact ⟨trivial, by simp [hs]⟩
  obtain ⟨g, hg0, hgm, hgpath, -, -⟩ := H.concatenate_two_paths hp hq (by simp [hpn])
  exact ⟨g, n + 1, hg0.trans hp0, hgm.trans (by simp), hgpath⟩

/-- walkup 前后的 `goOneStep` 在避开接缝点的位置上一致
（`edgeMap_walkup`/`nodeMap_walkup`/`faceMap_walkup` 第三分量的合取形式）。 -/
theorem goOneStep_edgeWalkup_iff (H : Hypermap α) {x z w : α}
    (h1 : z ≠ x) (h2 : z ≠ H.nodeMap.symm x) (h3 : z ≠ H.faceMap.symm x)
    (h4 : z ≠ H.nodeMap x) (h5 : z ≠ H.edgeMap⁻¹ x) :
    H.goOneStep z w ↔ (H.edgeWalkup x).goOneStep z w := by
  have he : (H.edgeWalkup x).edgeMap z = H.edgeMap z :=
    (H.edgeMap_walkup x z).2.2.2 ⟨h1, h5, h4⟩
  have hn : (H.edgeWalkup x).nodeMap z = H.nodeMap z :=
    (H.nodeMap_walkup x z).2.2 ⟨h1, h2⟩
  have hf : (H.edgeWalkup x).faceMap z = H.faceMap z :=
    (H.faceMap_walkup x z).2.2 ⟨h1, h3⟩
  unfold goOneStep
  rw [he, hn, hf]

/-- 路径上每个点都避开接缝点时，`isPath` 在 walkup 前后一致。 -/
theorem isPath_edgeWalkup_iff (H : Hypermap α) {p : ℕ → α} {n : ℕ} {x : α}
    (h : ∀ i ≤ n, p i ≠ x ∧ p i ≠ H.nodeMap.symm x ∧ p i ≠ H.faceMap.symm x ∧
      p i ≠ H.nodeMap x ∧ p i ≠ H.edgeMap⁻¹ x) :
    H.isPath p n ↔ (H.edgeWalkup x).isPath p n := by
  rw [H.isPath_iff, (H.edgeWalkup x).isPath_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  obtain ⟨h1, h2, h3, h4, h5⟩ := h i (Nat.le_of_lt hi)
  exact H.goOneStep_edgeWalkup_iff h1 h2 h3 h4 h5

/-- `hypermap.hl`:3089 `lemma_walkup_first_component_eq`。 -/
theorem walkup_first_component_eq (H : Hypermap α) {x y : α}
    (_hx : x ∈ H.darts) (hy : x ∉ H.combComponent y) :
    H.combComponent y = (H.edgeWalkup x).combComponent y ∧
      H.nodeMap x ∉ H.combComponent y ∧ H.edgeMap⁻¹ x ∉ H.combComponent y := by
  -- 关键观察：`comp y` 中的点都避开五个接缝点（否则 `comp y = comp x`）。
  have key : ∀ w ∈ H.combComponent x, ∀ z ∈ H.combComponent y, z ≠ w := by
    intro w hw z hz hzw
    apply hy
    have h1 : H.combComponent y = H.combComponent z := H.combComponent_eq_of_mem hz
    have h2 : H.combComponent z = H.combComponent x := by
      rw [hzw]; exact (H.combComponent_eq_of_mem hw).symm
    rw [h1, h2]
    exact H.mem_combComponent_self x
  obtain ⟨je, hje⟩ := H.edgeMap_permutes.exists_pow_symm_apply x
  obtain ⟨jn, hjn⟩ := H.nodeMap_permutes.exists_pow_symm_apply x
  obtain ⟨jf, hjf⟩ := H.faceMap_permutes.exists_pow_symm_apply x
  have hav : ∀ z ∈ H.combComponent y,
      z ≠ x ∧ z ≠ H.nodeMap.symm x ∧ z ≠ H.faceMap.symm x ∧
        z ≠ H.nodeMap x ∧ z ≠ H.edgeMap⁻¹ x := by
    intro z hz
    refine ⟨key x (H.mem_combComponent_self x) z hz, ?_, ?_, ?_, ?_⟩
    · rw [hjn]; exact key _ (H.powers_in_component x jn).2.1 z hz
    · rw [hjf]; exact key _ (H.powers_in_component x jf).2.2 z hz
    · exact key (H.nodeMap x) (H.powers_in_component x 1).2.1 z hz
    · show z ≠ H.edgeMap.symm x
      rw [hje]; exact key _ (H.powers_in_component x je).1 z hz
  refine ⟨?_, fun h => (hav _ h).2.2.2.1 rfl, fun h => (hav _ h).2.2.2.2 rfl⟩
  ext z
  constructor
  · rintro ⟨p, m, hp0, hpm, hp⟩
    have hpts : ∀ i ≤ m, p i ∈ H.combComponent y :=
      fun i hi => ⟨p, i, hp0, rfl, H.isPath_mono hp hi⟩
    exact ⟨p, m, hp0, hpm, (H.isPath_edgeWalkup_iff (fun i hi => hav _ (hpts i hi))).mp hp⟩
  · rintro ⟨p, m, hp0, hpm, hp⟩
    have hIH : ∀ k ≤ m, H.isPath p k ∧ p k ∈ H.combComponent y := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨trivial, by rw [hp0]; exact H.mem_combComponent_self y⟩
      | succ k ih =>
        intro hkm
        obtain ⟨hpk, hmem⟩ := ih (Nat.le_of_succ_le hkm)
        have hstep : (H.edgeWalkup x).goOneStep (p k) (p (k + 1)) :=
          ((H.edgeWalkup x).isPath_iff p m).mp hp k hkm
        obtain ⟨h1, h2, h3, h4, h5⟩ := hav _ hmem
        have hstepH : H.goOneStep (p k) (p (k + 1)) :=
          (H.goOneStep_edgeWalkup_iff h1 h2 h3 h4 h5).mpr hstep
        exact ⟨(H.isPath_succ p k).mpr ⟨hpk, hstepH⟩,
          H.isInComponent_trans_step ⟨p, k, hp0, rfl, hpk⟩ hstepH⟩
    exact ⟨p, m, hp0, hpm, (hIH m le_rfl).1⟩

/-- `hypermap.hl`:3272 `lemma_walkup_second_component_eq`。 -/
theorem walkup_second_component_eq (H : Hypermap α) {x y : α}
    (_hx : x ∈ H.darts) (hy : y ∈ H.darts) (hyx : y ≠ x)
    (h4 : H.edgeMap⁻¹ x ∉ (H.edgeWalkup x).combComponent y)
    (h5 : H.nodeMap x ∉ (H.edgeWalkup x).combComponent y) :
    H.combComponent y = (H.edgeWalkup x).combComponent y ∧ y ∉ H.combComponent x := by
  have hyE : y ∈ H.darts.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
  -- walkup 侧组件中的点避开五个接缝点（逐条证明，后面的情形会用到前面的）
  have havx : ∀ z ∈ (H.edgeWalkup x).combComponent y, z ≠ x := by
    intro z hz
    have hsub := (H.edgeWalkup x).combComponent_subset_darts hyE hz
    exact (Finset.mem_erase.mp hsub).1
  have hcomp_eq : ∀ z ∈ (H.edgeWalkup x).combComponent y,
      (H.edgeWalkup x).combComponent z = (H.edgeWalkup x).combComponent y :=
    fun z hz => ((H.edgeWalkup x).combComponent_eq_of_mem hz).symm
  have havn : ∀ z ∈ (H.edgeWalkup x).combComponent y, z ≠ H.nodeMap.symm x := by
    -- 否则 n' z = n x ∈ comp G z = comp G y，与 h5 矛盾
    intro z hz hcon
    apply h5
    have h2 : (H.edgeWalkup x).nodeMap z = H.nodeMap x := by
      rw [hcon]; exact (H.nodeMap_walkup x x).2.1
    have h1 : H.nodeMap x ∈ (H.edgeWalkup x).combComponent z := by
      rw [← h2]
      exact (H.edgeWalkup x).powers_in_component z 1 |>.2.1
    rwa [hcomp_eq z hz] at h1
  have havf : ∀ z ∈ (H.edgeWalkup x).combComponent y, z ≠ H.faceMap.symm x := by
    -- 分三种退化情形（对应 HOL 证明中的 F12）
    intro z hz hcon
    by_cases hf1 : H.faceMap.symm x = x
    · exact havx z hz (by rw [hcon, hf1])
    · by_cases he1 : H.edgeMap⁻¹ x = x
      · -- e⁻¹ x = x ⟹ f x = n⁻¹ x，于是 n⁻¹ x = f' z ∈ comp G z，与 havn 矛盾
        have he : H.edgeMap x = x := (Perm_apply_eq_self_iff_symm _ _).mpr he1
        have hfe : H.faceMap x = H.nodeMap.symm x := (H.edgeMap_fixed_iff x).mp he
        have h2 : (H.edgeWalkup x).faceMap z = H.faceMap x := by
          rw [hcon]; exact (H.faceMap_walkup x x).2.1
        have h1 : H.nodeMap.symm x ∈ (H.edgeWalkup x).combComponent z := by
          rw [← hfe, ← h2]
          exact (H.edgeWalkup x).powers_in_component z 1 |>.2.2
        rw [hcomp_eq z hz] at h1
        exact havn _ h1 rfl
      · -- 非退化情形：e' (e⁻¹ x) = f⁻¹ x，于是 e⁻¹ x = e'⁻¹ z ∈ comp G z，与 h4 矛盾
        have hee : (H.edgeWalkup x).edgeMap (H.edgeMap⁻¹ x) = H.faceMap⁻¹ x :=
          (H.edgeMap_walkup x x).2.2.1 ⟨hf1, he1⟩
        have h2 : H.edgeMap⁻¹ x = (H.edgeWalkup x).edgeMap.symm z := by
          have h3 : (H.edgeWalkup x).edgeMap.symm z = H.edgeMap⁻¹ x := by
            rw [hcon]
            show (H.edgeWalkup x).edgeMap.symm (H.faceMap⁻¹ x) = H.edgeMap⁻¹ x
            rw [← hee]
            exact Equiv.symm_apply_apply _ _
          exact h3.symm
        have h1 : H.edgeMap⁻¹ x ∈ (H.edgeWalkup x).combComponent z := by
          rw [h2]
          exact (H.edgeWalkup x).inverses_in_component z |>.1
        rw [hcomp_eq z hz] at h1
        exact h4 h1
  have hav : ∀ z ∈ (H.edgeWalkup x).combComponent y,
      z ≠ x ∧ z ≠ H.nodeMap.symm x ∧ z ≠ H.faceMap.symm x ∧
        z ≠ H.nodeMap x ∧ z ≠ H.edgeMap⁻¹ x :=
    fun z hz => ⟨havx z hz, havn z hz, havf z hz,
      fun hcon => h5 (hcon ▸ hz), fun hcon => h4 (hcon ▸ hz)⟩
  have hFF : H.combComponent y = (H.edgeWalkup x).combComponent y := by
    ext z
    constructor
    · rintro ⟨p, m, hp0, hpm, hp⟩
      have hIH : ∀ k ≤ m, (H.edgeWalkup x).isPath p k ∧
          p k ∈ (H.edgeWalkup x).combComponent y := by
        intro k
        induction k with
        | zero =>
          intro _
          exact ⟨trivial, by rw [hp0]; exact (H.edgeWalkup x).mem_combComponent_self y⟩
        | succ k ih =>
          intro hkm
          obtain ⟨hpk, hmem⟩ := ih (Nat.le_of_succ_le hkm)
          have hstep : H.goOneStep (p k) (p (k + 1)) := (H.isPath_iff p m).mp hp k hkm
          obtain ⟨h1, h2, h3, h4, h5⟩ := hav _ hmem
          have hstepG : (H.edgeWalkup x).goOneStep (p k) (p (k + 1)) :=
            (H.goOneStep_edgeWalkup_iff h1 h2 h3 h4 h5).mp hstep
          exact ⟨((H.edgeWalkup x).isPath_succ p k).mpr ⟨hpk, hstepG⟩,
            (H.edgeWalkup x).isInComponent_trans_step ⟨p, k, hp0, rfl, hpk⟩ hstepG⟩
      exact ⟨p, m, hp0, hpm, (hIH m le_rfl).1⟩
    · rintro ⟨p, m, hp0, hpm, hp⟩
      have hpts : ∀ i ≤ m, p i ∈ (H.edgeWalkup x).combComponent y :=
        fun i hi => ⟨p, i, hp0, rfl, (H.edgeWalkup x).isPath_mono hp hi⟩
      exact ⟨p, m, hp0, hpm,
        (H.isPath_edgeWalkup_iff (fun i hi => hav _ (hpts i hi))).mpr hp⟩
  refine ⟨hFF, ?_⟩
  intro hcon
  have h1 : x ∈ H.combComponent y := H.combComponent_symmetry hcon
  rw [hFF] at h1
  exact (hav x h1).1 rfl

/-- `hypermap.hl`:3436 `lemma_walkup_components`。 -/
theorem setOfComponents_walkup (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.setOfComponents \ {H.combComponent x} =
      (H.edgeWalkup x).setOfComponents \
        {(H.edgeWalkup x).combComponent (H.nodeMap x),
          (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x)} := by
  ext u
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h4⟩
    have h5 : x ∉ H.combComponent y := fun hcon => h4 (H.combComponent_eq_of_mem hcon)
    obtain ⟨horbit, h7, h8⟩ := H.walkup_first_component_eq hx h5
    have hyx : y ≠ x := fun h => h4 (by rw [h])
    refine ⟨⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩, horbit.symm⟩, ?_, ?_⟩
    · intro hcon
      apply h7
      show H.nodeMap x ∈ H.combComponent y
      exact hcon.symm ▸ (H.edgeWalkup x).mem_combComponent_self _
    · intro hcon
      apply h8
      show H.edgeMap⁻¹ x ∈ H.combComponent y
      exact hcon.symm ▸ (H.edgeWalkup x).mem_combComponent_self _
  · rintro ⟨⟨y, hy, rfl⟩, h4, h5⟩
    have hy' : y ∈ H.darts.erase x := hy
    rw [Finset.mem_erase] at hy'
    obtain ⟨hyx, hyD⟩ := hy'
    have h6 : H.nodeMap x ∉ (H.edgeWalkup x).combComponent y := fun hcon =>
      h4 ((H.edgeWalkup x).combComponent_eq_of_mem hcon)
    have h7 : H.edgeMap⁻¹ x ∉ (H.edgeWalkup x).combComponent y := fun hcon =>
      h5 ((H.edgeWalkup x).combComponent_eq_of_mem hcon)
    obtain ⟨horbit, h8⟩ := H.walkup_second_component_eq hx hyD hyx h7 h6
    refine ⟨⟨y, hyD, horbit⟩, ?_⟩
    intro hcon
    apply h8
    rw [← hcon]
    exact (H.edgeWalkup x).mem_combComponent_self y

/-- `hypermap.hl`:2744 `lemma_complement_two_edges`。 -/
theorem complement_two_edges (H : Hypermap α) (hx : x ∈ H.darts) (hy : y ∈ H.darts) :
    H.edge x ∪ H.edge y = ↑H.darts \ ⋃₀ (H.edgeSet \ {H.edge x, H.edge y}) := by
  ext z
  constructor
  · intro hz
    have key : z ∉ ⋃₀ (H.edgeSet \ {H.edge x, H.edge y}) := by
      intro hmem
      rw [Set.mem_sUnion] at hmem
      obtain ⟨t, ht, hzt⟩ := hmem
      obtain ⟨htE, htnot⟩ := ht
      obtain ⟨v, hv, rfl⟩ := htE
      have hzv : H.edge v = H.edge z := H.edge_eq_of_mem hzt
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htnot
      rcases hz with hz1 | hz1
      · exact htnot.1 (hzv.trans (H.edge_eq_of_mem hz1).symm)
      · exact htnot.2 (hzv.trans (H.edge_eq_of_mem hz1).symm)
    rcases hz with hz | hz
    · exact ⟨H.edge_subset_darts hx hz, key⟩
    · exact ⟨H.edge_subset_darts hy hz, key⟩
  · intro hz
    obtain ⟨hzD, hznot⟩ := hz
    by_cases hx' : H.edge z = H.edge x
    · exact Or.inl (hx' ▸ H.mem_edge_self z)
    · by_cases hy' : H.edge z = H.edge y
      · exact Or.inr (hy' ▸ H.mem_edge_self z)
      · exfalso
        apply hznot
        apply Set.mem_sUnion.mpr
        exact ⟨H.edge z, ⟨(H.mem_darts_iff_edge_mem z).mp hzD, by
          rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hx', hy'⟩⟩, H.mem_edge_self z⟩

/-- `hypermap.hl`:2791 `lemma_edge_map_walkup_in_dart`。 -/
theorem edgeMap_walkup_mem_darts (H : Hypermap α) (hx : x ∈ H.darts)
    (h : H.edgeMap x ≠ x) :
    H.edgeMap x ∈ (H.edgeWalkup x).darts ∧ H.edgeMap⁻¹ x ∈ (H.edgeWalkup x).darts := by
  show H.edgeMap x ∈ H.darts.erase x ∧ H.edgeMap⁻¹ x ∈ H.darts.erase x
  exact ⟨Finset.mem_erase.mpr ⟨h, H.edgeMap_apply_mem hx⟩,
    Finset.mem_erase.mpr ⟨(Perm_apply_ne_self_iff_symm _ _).mp h, H.edgeMap_symm_apply_mem hx⟩⟩

/-- `hypermap.hl`:2801 `lemma_node_map_walkup_in_dart`。 -/
theorem nodeMap_walkup_mem_darts (H : Hypermap α) (hx : x ∈ H.darts)
    (h : H.nodeMap x ≠ x) :
    H.nodeMap x ∈ (H.edgeWalkup x).darts ∧ H.nodeMap⁻¹ x ∈ (H.edgeWalkup x).darts := by
  show H.nodeMap x ∈ H.darts.erase x ∧ H.nodeMap⁻¹ x ∈ H.darts.erase x
  exact ⟨Finset.mem_erase.mpr ⟨h, H.nodeMap_apply_mem hx⟩,
    Finset.mem_erase.mpr ⟨(Perm_apply_ne_self_iff_symm _ _).mp h, H.nodeMap_symm_apply_mem hx⟩⟩

/-- `hypermap.hl`:2810 `lemma_face_map_walkup_in_dart`。 -/
theorem faceMap_walkup_mem_darts (H : Hypermap α) (hx : x ∈ H.darts)
    (h : H.faceMap x ≠ x) :
    H.faceMap x ∈ (H.edgeWalkup x).darts ∧ H.faceMap⁻¹ x ∈ (H.edgeWalkup x).darts := by
  show H.faceMap x ∈ H.darts.erase x ∧ H.faceMap⁻¹ x ∈ H.darts.erase x
  exact ⟨Finset.mem_erase.mpr ⟨h, H.faceMap_apply_mem hx⟩,
    Finset.mem_erase.mpr ⟨(Perm_apply_ne_self_iff_symm _ _).mp h, H.faceMap_symm_apply_mem hx⟩⟩

/-- `hypermap.hl`:2819 `lemma_walkup_support_edges`。 -/
theorem walkup_support_edges (H : Hypermap α) (hx : x ∈ H.darts)
    (hnd : H.DartNondegenerate x) :
    H.edge x ∪ H.edge (H.nodeMap x) =
      {x} ∪ ((H.edgeWalkup x).edge (H.nodeMap x) ∪
        (H.edgeWalkup x).edge (H.edgeMap⁻¹ x)) := by
  have hnx : H.nodeMap x ∈ H.darts := H.nodeMap_apply_mem hx
  have h1 := H.complement_two_edges hx hnx
  have hnxG : H.nodeMap x ∈ (H.edgeWalkup x).darts :=
    (H.nodeMap_walkup_mem_darts hx hnd.2.1).1
  have hexG : H.edgeMap⁻¹ x ∈ (H.edgeWalkup x).darts :=
    (H.edgeMap_walkup_mem_darts hx hnd.1).2
  have h2 := (H.edgeWalkup x).complement_two_edges hnxG hexG
  have h3 := H.edgeSet_walkup hx
  have hxU : x ∉ ⋃₀ (H.edgeSet \ {H.edge x, H.edge (H.nodeMap x)}) := by
    intro hmem
    rw [Set.mem_sUnion] at hmem
    obtain ⟨t, ht, hxt⟩ := hmem
    obtain ⟨htE, htnot⟩ := ht
    obtain ⟨u, hu, rfl⟩ := htE
    have h4 : H.edge u = H.edge x := H.edge_eq_of_mem hxt
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htnot
    exact htnot.1 h4
  rw [h3] at hxU
  rw [h1, h3, h2]
  ext z
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · intro ⟨hzD, hzU⟩
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr ⟨Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzx, hzD⟩), hzU⟩
  · intro hz
    rcases hz with rfl | ⟨hzE, hzU⟩
    · exact ⟨hx, hxU⟩
    · exact ⟨(Finset.mem_erase.mp (Finset.mem_coe.mp hzE)).2, hzU⟩

/-- `hypermap.hl`:2850 `lemma_in_edge`。 -/
theorem mem_edge_iff (H : Hypermap α) (x y : α) :
    y ∈ H.edge x ↔ ∃ j : ℕ, y = (H.edgeMap ^ j) x := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, hj.symm⟩
  · rintro ⟨j, hj⟩; exact ⟨j, hj.symm⟩

/-- `hypermap.hl`:2853 `lemma_in_edge2`。 -/
theorem pow_edgeMap_mem_edge (H : Hypermap α) (x : α) (n : ℕ) :
    (H.edgeMap ^ n) x ∈ H.edge x := pow_apply_mem_orbitMap _ _ _

/-- `hypermap.hl`:2855 `lemma_edge_cycle`。 -/
theorem edgeMap_pow_card_edge (H : Hypermap α) (x : α) :
    (H.edgeMap ^ ((H.edge x).ncard)) x = x :=
  H.edgeMap_permutes.pow_ncard_orbitMap_apply_self x

/-- 幂链辅助：`(p ^ (k - 1)) (p x) = (p ^ k) x`（`k ≥ 1`）。 -/
theorem Perm.pow_pred_apply {α : Type*} (p : Equiv.Perm α) {k : ℕ} (hk : 0 < k) (x : α) :
    (p ^ (k - 1)) (p x) = (p ^ k) x := by
  rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hk]

/-- `hypermap.hl`:2860 `lemma_edge_split`（split 情形：walkup 把 `x` 所在的边拆开）。 -/
theorem edge_split (H : Hypermap α) {x : α} (hx : x ∈ H.darts) (hsplit : H.IsEdgeSplit x) :
    H.faceMap⁻¹ x ∉ (H.edgeWalkup x).edge (H.nodeMap x) ∧
      H.edge x = {x} ∪ ((H.edgeWalkup x).edge (H.nodeMap x) ∪
        (H.edgeWalkup x).edge (H.faceMap⁻¹ x)) := by
  obtain ⟨hnd, hnx⟩ := hsplit
  set e' := (H.edgeWalkup x).edgeMap with he'
  -- `n x = (e^k) x` 且 `k + 1 < card (edge x)`
  obtain ⟨k, hklt, hkeq⟩ := H.edgeMap_permutes.exists_lt_ncard_pow_apply hnx
  have hEc : (orbitMap H.edgeMap x).ncard = (H.edge x).ncard := rfl
  rw [hEc] at hklt
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hkeq
    simp at hkeq
    exact hnd.2.1 hkeq
  have hfk : H.faceMap⁻¹ x = (H.edgeMap ^ (k + 1)) x := by
    have h1 : H.faceMap⁻¹ x = H.edgeMap (H.nodeMap x) := by
      rw [H.inverse_hypermap_maps.2.2]; rfl
    rw [h1, hkeq, pow_succ', Equiv.Perm.mul_apply]
  have hk1 : k + 1 < (H.edge x).ncard := by
    by_contra hge
    have hkc : k + 1 = (H.edge x).ncard := by omega
    have hfx : H.faceMap x = x := by
      have h2 : H.faceMap⁻¹ x = x := by
        rw [hfk, hkc]
        exact H.edgeMap_pow_card_edge x
      exact (Perm_apply_eq_self_iff_symm _ _).mpr h2
    exact hnd.2.2 hfx
  -- 幂链：`i < k` 时 `(e'^i) (e x) = (e^i) (e x)`
  have hinj : injOrbit H.edgeMap x ((H.edge x).ncard - 1) := by
    apply H.edgeMap_permutes.injOrbit_of_lt_ncard
    rw [hEc]
    omega
  rw [injOrbit_iff_pairwise] at hinj
  have hpart2 : e' (H.nodeMap x) = H.edgeMap x := (H.edgeMap_walkup x x).2.1 ⟨hnd.2.1, hnd.1⟩
  have hchain : ∀ i < k, (e' ^ i) (H.edgeMap x) = (H.edgeMap ^ i) (H.edgeMap x) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hik
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
      have hpa : (H.edgeMap ^ i) (H.edgeMap x) = (H.edgeMap ^ (i + 1)) x :=
        Perm.pow_pred_apply (p := H.edgeMap) (k := i + 1) (by omega) x
      have h1 : (H.edgeMap ^ i) (H.edgeMap x) ≠ x := by
        rw [hpa]
        intro hcon
        have h2 := hinj (i + 1) 0 (by omega) (by omega) (by simpa using hcon)
        omega
      have h2 : (H.edgeMap ^ i) (H.edgeMap x) ≠ H.edgeMap⁻¹ x := by
        rw [hpa]
        intro hcon
        have h3 : (H.edgeMap ^ (i + 2)) x = x := by
          have h4 : H.edgeMap ((H.edgeMap ^ (i + 1)) x) = x := by
            rw [hcon]; show H.edgeMap (H.edgeMap.symm x) = x; exact Equiv.apply_symm_apply _ _
          rwa [pow_succ', Equiv.Perm.mul_apply]
        have h5 := hinj (i + 2) 0 (by omega) (by omega) (by simpa using h3)
        omega
      have h3 : (H.edgeMap ^ i) (H.edgeMap x) ≠ H.nodeMap x := by
        rw [hpa, hkeq]
        intro hcon
        have h4 := hinj (i + 1) k (by omega) (by omega) hcon
        omega
      rw [(H.edgeMap_walkup x _).2.2.2 ⟨h1, h2, h3⟩, pow_succ', Equiv.Perm.mul_apply]
  -- `(e'^k) (n x) = n x`，故 `orbit e' (n x)` 由前 `k` 个幂组成
  have hcycle : (e' ^ k) (H.nodeMap x) = H.nodeMap x := by
    rw [(by omega : k = k - 1 + 1), pow_succ, Equiv.Perm.mul_apply, hpart2,
      hchain (k - 1) (by omega)]
    have hpa : (H.edgeMap ^ (k - 1)) (H.edgeMap x) = (H.edgeMap ^ k) x :=
      Perm.pow_pred_apply (p := H.edgeMap) (k := k) (by omega) x
    rw [hpa, ← hkeq]
  have horb : (H.edgeWalkup x).edge (H.nodeMap x) =
      (fun m => (e' ^ m) (H.nodeMap x)) '' ↑(Finset.range k) := orbit_cyclic e' hk0 hcycle
  refine ⟨?_, ?_⟩
  · -- `f⁻¹ x = (e^(k+1)) x ∉ orbit e' (n x)`：与前 `k` 个幂比对并用 `injOrbit` 排除
    intro hmem
    rw [horb] at hmem
    obtain ⟨m, hmk, hm⟩ := hmem
    change (e' ^ m) (H.nodeMap x) = H.faceMap⁻¹ x at hm
    rw [hfk] at hm
    have hmk' : m < k := Finset.mem_range.mp hmk
    rcases (by omega : m = 0 ∨ 1 ≤ m) with rfl | hm1
    · simp at hm
      have h4 : (H.edgeMap ^ (k + 1)) x = (H.edgeMap ^ k) x := hm.symm.trans hkeq
      have h5 := hinj (k + 1) k (by omega) (by omega) h4
      omega
    · have h4 : (e' ^ m) (H.nodeMap x) = (H.edgeMap ^ m) x := by
        conv_lhs => rw [(by omega : m = m - 1 + 1)]
        rw [pow_succ, Equiv.Perm.mul_apply, hpart2, hchain (m - 1) (by omega)]
        exact Perm.pow_pred_apply (p := H.edgeMap) (k := m) (by omega) x
      rw [h4] at hm
      have h5 := hinj (k + 1) m (by omega) (by omega) hm.symm
      omega
  · -- `edge H x = {x} ∪ G.edge (n x) ∪ G.edge (f⁻¹ x)`：由 `walkup_support_edges` 代入两条恒等
    have hsup := H.walkup_support_edges hx hnd
    have hid1 : H.edge (H.nodeMap x) = H.edge x := (H.edge_eq_of_mem hnx).symm
    have hpart3 : e' (H.edgeMap⁻¹ x) = H.faceMap⁻¹ x :=
      (H.edgeMap_walkup x x).2.2.1
        ⟨(Perm_apply_ne_self_iff_symm _ _).mp hnd.2.2,
          (Perm_apply_ne_self_iff_symm _ _).mp hnd.1⟩
    have hid2 : (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) = (H.edgeWalkup x).edge (H.faceMap⁻¹ x) :=
      (H.edgeWalkup x).edge_eq_of_mem (hpart3 ▸ (H.edgeWalkup x).pow_edgeMap_mem_edge _ 1)
    rw [hid1, Set.union_self, hid2] at hsup
    exact hsup

/-- `hypermap.hl`:2966 `lemma_edge_merge`（merge 情形）。 -/
theorem edge_merge (H : Hypermap α) {x : α} (hx : x ∈ H.darts) (hmerge : H.IsEdgeMerge x) :
    {x} ∪ (H.edgeWalkup x).edge (H.nodeMap x) = H.edge x ∪ H.edge (H.nodeMap x) := by
  obtain ⟨hnd, hnx⟩ := hmerge
  set e' := (H.edgeWalkup x).edgeMap with he'
  -- `e⁻¹ x = (e^k) x`，`1 ≤ k < card (edge x)`
  have hinv : H.edgeMap⁻¹ x ∈ H.edge x := H.edgeMap_permutes.symm_apply_mem_orbitMap x
  obtain ⟨k, hklt, hkeq⟩ := H.edgeMap_permutes.exists_lt_ncard_pow_apply hinv
  have hEc : (orbitMap H.edgeMap x).ncard = (H.edge x).ncard := rfl
  rw [hEc] at hklt
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hkeq
    simp at hkeq
    exact (Perm_apply_ne_self_iff_symm _ _).mp hnd.1 hkeq
  have hinj : injOrbit H.edgeMap x ((H.edge x).ncard - 1) := by
    apply H.edgeMap_permutes.injOrbit_of_lt_ncard
    rw [hEc]
    omega
  rw [injOrbit_iff_pairwise] at hinj
  have hpart2 : e' (H.nodeMap x) = H.edgeMap x := (H.edgeMap_walkup x x).2.1 ⟨hnd.2.1, hnd.1⟩
  have hchain : ∀ i < k, (e' ^ i) (H.edgeMap x) = (H.edgeMap ^ i) (H.edgeMap x) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hik
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
      have hpa : (H.edgeMap ^ i) (H.edgeMap x) = (H.edgeMap ^ (i + 1)) x :=
        Perm.pow_pred_apply (p := H.edgeMap) (k := i + 1) (by omega) x
      have h1 : (H.edgeMap ^ i) (H.edgeMap x) ≠ x := by
        rw [hpa]
        intro hcon
        have h2 := hinj (i + 1) 0 (by omega) (by omega) (by simpa using hcon)
        omega
      have h2 : (H.edgeMap ^ i) (H.edgeMap x) ≠ H.edgeMap⁻¹ x := by
        rw [hpa, hkeq]
        intro hcon
        have h3 := hinj (i + 1) k (by omega) (by omega) hcon
        omega
      have h3 : (H.edgeMap ^ i) (H.edgeMap x) ≠ H.nodeMap x := by
        rw [hpa]
        intro hcon
        exact hnx ⟨i + 1, hcon⟩
      rw [(H.edgeMap_walkup x _).2.2.2 ⟨h1, h2, h3⟩, pow_succ', Equiv.Perm.mul_apply]
  -- `(e'^k) (n x) = e⁻¹ x`，故 `G.edge (e⁻¹ x) = G.edge (n x)`
  have hcycle : (e' ^ k) (H.nodeMap x) = H.edgeMap⁻¹ x := by
    rw [(by omega : k = k - 1 + 1), pow_succ, Equiv.Perm.mul_apply, hpart2,
      hchain (k - 1) (by omega)]
    have hpa : (H.edgeMap ^ (k - 1)) (H.edgeMap x) = (H.edgeMap ^ k) x :=
      Perm.pow_pred_apply (p := H.edgeMap) (k := k) (by omega) x
    rw [hpa, ← hkeq]
  have hid : (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) = (H.edgeWalkup x).edge (H.nodeMap x) :=
    ((H.edgeWalkup x).edge_eq_of_mem ⟨k, hcycle⟩).symm
  have hsup := H.walkup_support_edges hx hnd
  rw [hid, Set.union_self] at hsup
  exact hsup.symm

end Hypermap

/-- `hypermap.hl`:1689 `lemma_hypermap_eq` 的结构版：hypermap 由 dart 集合与三个映射决定。 -/
theorem Hypermap.ext' {α : Type*} [DecidableEq α] {H1 H2 : Hypermap α}
    (hd : H1.darts = H2.darts) (he : H1.edgeMap = H2.edgeMap)
    (hn : H1.nodeMap = H2.nodeMap) (hf : H1.faceMap = H2.faceMap) : H1 = H2 := by
  rcases H1 with ⟨D1, e1, n1, f1, a1, b1, c1, d1⟩
  rcases H2 with ⟨D2, e2, n2, f2, a2, b2, c2, d2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : D1 = D2 ∧ e1 = e2 ∧ n1 = n2 ∧ f1 = f2 := ⟨hd, he, hn, hf⟩
  rfl

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `(H.edgeWalkup x).edgeMap z = w` 的正规形（`edgeMap_walkup` 证明中 `key` 的独立版本）。 -/
theorem edgeWalkup_edgeMap_eq_iff (H : Hypermap α) (x z w : α) :
    (H.edgeWalkup x).edgeMap z = w ↔
      (Equiv.swap x (H.nodeMap x) * H.nodeMap)
        ((Equiv.swap x (H.faceMap x) * H.faceMap) w) = z := by
  show ((Equiv.swap x (H.faceMap x) * H.faceMap)⁻¹ *
    (Equiv.swap x (H.nodeMap x) * H.nodeMap)⁻¹) z = w ↔ _
  rw [Equiv.Perm.mul_apply, Perm_inv_apply_inv_apply_iff]

/-- `hypermap.hl`:3511 `edge_degenerate_walkup_edge_map`。 -/
theorem edge_degenerate_walkup_edgeMap (H : Hypermap α) {x : α} (_hx : x ∈ H.darts)
    (h : H.edgeMap x = x) (y : α) : (H.edgeWalkup x).edgeMap y = H.edgeMap y := by
  by_cases hyx : y = x
  · rw [hyx, (H.edgeMap_walkup x y).1, h]
  · by_cases hyn : y = H.nodeMap x
    · subst hyn
      have hfe : H.faceMap x = H.nodeMap.symm x := (H.edgeMap_fixed_iff x).mp h
      rw [H.edgeWalkup_edgeMap_eq_iff]
      have hen : H.edgeMap (H.nodeMap x) = H.faceMap⁻¹ x := by
        rw [H.inverse_hypermap_maps.2.2]; rfl
      rw [hen]
      have h3 : (Equiv.swap x (H.faceMap x) * H.faceMap) (H.faceMap⁻¹ x) = H.faceMap x :=
        (H.faceMap_walkup x x).2.1
      rw [h3, hfe]
      exact (H.nodeMap_walkup x x).2.1
    · exact (H.edgeMap_walkup x y).2.2.2 ⟨hyx, by
        have h2 : H.edgeMap⁻¹ x = x := (Perm_apply_eq_self_iff_symm _ _).mp h
        rwa [h2], hyn⟩

/-- `hypermap.hl`:3540 `node_degenerate_walkup_node_map`。 -/
theorem node_degenerate_walkup_nodeMap (H : Hypermap α) {x : α} (_hx : x ∈ H.darts)
    (h : H.nodeMap x = x) (y : α) : (H.edgeWalkup x).nodeMap y = H.nodeMap y := by
  by_cases hyx : y = x
  · rw [hyx, (H.nodeMap_walkup x y).1, h]
  · have h2 : H.nodeMap.symm x = x := (Perm_apply_eq_self_iff_symm _ _).mp h
    exact (H.nodeMap_walkup x y).2.2 ⟨hyx, by rwa [h2]⟩

/-- `hypermap.hl`:3553 `node_degenerate_walkup_edge_map`。 -/
theorem node_degenerate_walkup_edgeMap (H : Hypermap α) {x : α} (_hx : x ∈ H.darts)
    (h : H.nodeMap x = x) :
    (H.edgeWalkup x).edgeMap x = x ∧ (H.edgeWalkup x).edgeMap (H.edgeMap⁻¹ x) = H.edgeMap x ∧
      ∀ y : α, y ≠ x → y ≠ H.edgeMap⁻¹ x → (H.edgeWalkup x).edgeMap y = H.edgeMap y := by
  refine ⟨(H.edgeMap_walkup x x).1, ?_,
    fun y h1 h2 => (H.edgeMap_walkup x y).2.2.2 ⟨h1, h2, by rwa [h]⟩⟩
  rw [H.edgeWalkup_edgeMap_eq_iff]
  have hef : H.edgeMap x = H.faceMap.symm x := (H.nodeMap_fixed_iff x).mp h
  by_cases hfx : H.faceMap x = x
  · have he : H.edgeMap x = x := by
      rw [hef]; exact (Perm_apply_eq_self_iff_symm _ _).mp hfx
    have he2 : H.edgeMap⁻¹ x = x := (Perm_apply_eq_self_iff_symm _ _).mp he
    have h1 : (Equiv.swap x (H.faceMap x) * H.faceMap) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have h2 : (Equiv.swap x (H.nodeMap x) * H.nodeMap) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    rw [he, he2, h1, h2]
  · have h4 : (Equiv.swap x (H.faceMap x) * H.faceMap) (H.faceMap.symm x) = H.faceMap x := by
      rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]
    rw [hef, h4]
    have h3 : (Equiv.swap x (H.nodeMap x) * H.nodeMap) (H.faceMap x) = H.nodeMap (H.faceMap x) :=
      (H.nodeMap_walkup x (H.faceMap x)).2.2 ⟨hfx, by
        rwa [(Perm_apply_eq_self_iff_symm _ _).mp h]⟩
    rw [h3]
    show H.nodeMap (H.faceMap x) = H.edgeMap⁻¹ x
    rw [H.inverse_hypermap_maps.1]; rfl

/-- `hypermap.hl`:3588 `face_degenerate_walkup_face_map`。 -/
theorem face_degenerate_walkup_faceMap (H : Hypermap α) {x : α} (_hx : x ∈ H.darts)
    (h : H.faceMap x = x) (y : α) : (H.edgeWalkup x).faceMap y = H.faceMap y := by
  by_cases hyx : y = x
  · rw [hyx, (H.faceMap_walkup x y).1, h]
  · have h2 : H.faceMap.symm x = x := (Perm_apply_eq_self_iff_symm _ _).mp h
    exact (H.faceMap_walkup x y).2.2 ⟨hyx, by rwa [h2]⟩

/-- `hypermap.hl`:3602 `face_degenerate_walkup_edge_map`。 -/
theorem face_degenerate_walkup_edgeMap (H : Hypermap α) {x : α} (_hx : x ∈ H.darts)
    (h : H.faceMap x = x) :
    (H.edgeWalkup x).edgeMap x = x ∧ (H.edgeWalkup x).edgeMap (H.edgeMap⁻¹ x) = H.edgeMap x ∧
      ∀ y : α, y ≠ x → y ≠ H.edgeMap⁻¹ x → (H.edgeWalkup x).edgeMap y = H.edgeMap y := by
  have hne : H.nodeMap x = H.edgeMap.symm x := (H.faceMap_fixed_iff x).mp h
  refine ⟨(H.edgeMap_walkup x x).1, ?_,
    fun y h1 h2 => (H.edgeMap_walkup x y).2.2.2 ⟨h1, h2, by rwa [hne]⟩⟩
  rw [H.edgeWalkup_edgeMap_eq_iff]
  by_cases hex : H.edgeMap x = x
  · have he2 : H.edgeMap⁻¹ x = x := (Perm_apply_eq_self_iff_symm _ _).mp hex
    have h1 : (Equiv.swap x (H.faceMap x) * H.faceMap) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have h2 : (Equiv.swap x (H.nodeMap x) * H.nodeMap) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    rw [hex, he2, h1, h2]
  · have h2 : H.edgeMap x ≠ H.faceMap.symm x := by
      intro hcon
      apply hex
      have h1 : H.faceMap (H.edgeMap x) = x := by
        rw [hcon]; show H.faceMap (H.faceMap.symm x) = x; exact Equiv.apply_symm_apply _ _
      have h2' : x = H.nodeMap x := (H.nfe_apply x).symm.trans (congrArg H.nodeMap h1)
      rw [hne] at h2'
      exact ((Equiv.symm_apply_eq H.edgeMap).mp h2'.symm).symm
    have hfx : (Equiv.swap x (H.faceMap x) * H.faceMap) (H.edgeMap x) = H.faceMap (H.edgeMap x) :=
      (H.faceMap_walkup x (H.edgeMap x)).2.2 ⟨hex, h2⟩
    rw [hfx]
    have hfe : H.faceMap (H.edgeMap x) = H.nodeMap.symm x :=
      ((Equiv.symm_apply_eq H.nodeMap).mpr (H.nfe_apply x).symm).symm
    have h5 : (Equiv.swap x (H.nodeMap x) * H.nodeMap) (H.nodeMap.symm x) = H.nodeMap x := by
      rw [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]
    rw [hfe, h5, hne]
    show H.edgeMap.symm x = H.edgeMap⁻¹ x
    rfl

/-- 两个 hypermap 的 `edgeMap`、`faceMap` 相等则 `nodeMap` 相等（`comp_eq_one` 的消去）。 -/
theorem nodeMap_eq_of_edgeMap_faceMap_eq {α : Type*} [DecidableEq α] {H1 H2 : Hypermap α}
    (he : H1.edgeMap = H2.edgeMap) (hf : H1.faceMap = H2.faceMap) :
    H1.nodeMap = H2.nodeMap := by
  have h1 : H1.nodeMap * H1.faceMap = H1.edgeMap⁻¹ := H1.nodeMap_mul_faceMap
  have h2 : H2.nodeMap * H2.faceMap = H2.edgeMap⁻¹ := H2.nodeMap_mul_faceMap
  rw [he, hf] at h1
  exact mul_right_cancel (h1.trans h2.symm)

/-- `hypermap.hl`:3654 `edge_degenerate_walkup_first_eq`。 -/
theorem edge_degenerate_walkup_first_eq (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (h : H.edgeMap x = x) : H.nodeWalkup x = H.edgeWalkup x := by
  have hE1 : (H.nodeWalkup x).edgeMap = H.edgeMap := by
    show Equiv.swap x (H.edgeMap x) * H.edgeMap = H.edgeMap
    rw [h, Equiv.swap_self]; exact one_mul _
  have hE2 : (H.edgeWalkup x).edgeMap = H.edgeMap :=
    Equiv.ext fun y => H.edge_degenerate_walkup_edgeMap hx h y
  have hE : (H.nodeWalkup x).edgeMap = (H.edgeWalkup x).edgeMap := hE1.trans hE2.symm
  exact Hypermap.ext' rfl hE (nodeMap_eq_of_edgeMap_faceMap_eq hE rfl) rfl

/-- `hypermap.hl`:3722 `edge_degenerate_walkup_second_eq`。 -/
theorem edge_degenerate_walkup_second_eq (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (h : H.edgeMap x = x) : H.faceWalkup x = H.edgeWalkup x := by
  have hE1 : (H.faceWalkup x).edgeMap = H.edgeMap := by
    show Equiv.swap x (H.edgeMap x) * H.edgeMap = H.edgeMap
    rw [h, Equiv.swap_self]; exact one_mul _
  have hE2 : (H.edgeWalkup x).edgeMap = H.edgeMap :=
    Equiv.ext fun y => H.edge_degenerate_walkup_edgeMap hx h y
  have hE : (H.faceWalkup x).edgeMap = (H.edgeWalkup x).edgeMap := hE1.trans hE2.symm
  have hN : (H.faceWalkup x).nodeMap = (H.edgeWalkup x).nodeMap := rfl
  have hF : (H.faceWalkup x).faceMap = (H.edgeWalkup x).faceMap := by
    have h1 : (H.faceWalkup x).edgeMap * (H.faceWalkup x).nodeMap =
        (H.faceWalkup x).faceMap⁻¹ := (H.faceWalkup x).edgeMap_mul_nodeMap
    have h2 : (H.edgeWalkup x).edgeMap * (H.edgeWalkup x).nodeMap =
        (H.edgeWalkup x).faceMap⁻¹ := (H.edgeWalkup x).edgeMap_mul_nodeMap
    rw [hE, hN] at h1
    exact inv_injective (h1.symm.trans h2)
  exact Hypermap.ext' rfl hE hN hF

/-- `hypermap.hl`:3797 `edge_degenerate_walkup_third_eq`。 -/
theorem edge_degenerate_walkup_third_eq (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (h : H.edgeMap x = x) : H.nodeWalkup x = H.faceWalkup x :=
  (H.edge_degenerate_walkup_first_eq hx h).trans (H.edge_degenerate_walkup_second_eq hx h).symm

/-- `hypermap.hl`:3806 `lemma_shift_cycle`。 -/
theorem shift_cycle (H : Hypermap α) : H.shift.shift.shift = H :=
  Hypermap.ext' rfl rfl rfl rfl

/-- `hypermap.hl`:3811 `lemma_eq_iff_shift_eq`。 -/
theorem eq_iff_shift_eq (H H' : Hypermap α) : H = H' ↔ H.shift = H'.shift := by
  constructor
  · intro h; subst h; rfl
  · intro h
    apply Hypermap.ext'
    · change H.shift.darts = H'.shift.darts; rw [h]
    · change H.shift.faceMap = H'.shift.faceMap; rw [h]
    · change H.shift.edgeMap = H'.shift.edgeMap; rw [h]
    · change H.shift.nodeMap = H'.shift.nodeMap; rw [h]

/-- `hypermap.hl`:3818 `lemma_degenerate_walkup_first_eq`。 -/
theorem degenerate_walkup_first_eq (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (h : H.DartDegenerate x) : H.nodeWalkup x = H.edgeWalkup x := by
  rcases h with he | hn | hf
  · exact H.edge_degenerate_walkup_first_eq hx he
  · have h1 : (H.shift).edgeMap x = x := hn
    have h2 := (H.shift).edge_degenerate_walkup_second_eq hx h1
    have h3 : (H.edgeWalkup x).shift = (H.shift).edgeWalkup x := by
      have h4 : (H.shift).faceWalkup x = (H.edgeWalkup x).shift := by
        show ((H.shift.shift.shift).edgeWalkup x).shift = (H.edgeWalkup x).shift
        rw [H.shift_cycle]
      rw [h4] at h2
      exact h2
    show (H.shift.edgeWalkup x).shift.shift = H.edgeWalkup x
    rw [← h3]
    exact (H.edgeWalkup x).shift_cycle
  · have h1 : (H.shift.shift).edgeMap x = x := hf
    have h2 := (H.shift.shift).edge_degenerate_walkup_third_eq hx h1
    have h3 : (H.edgeWalkup x).shift.shift = (H.shift.edgeWalkup x).shift := by
      have h4 : (H.shift.shift).nodeWalkup x = (H.edgeWalkup x).shift.shift := by
        show ((H.shift.shift.shift).edgeWalkup x).shift.shift = _
        rw [H.shift_cycle]
      have h5 : (H.shift.shift).faceWalkup x = (H.shift.edgeWalkup x).shift := by
        show ((H.shift.shift.shift.shift).edgeWalkup x).shift = _
        rw [show H.shift.shift.shift.shift = H.shift from H.shift.shift_cycle]
      rw [h4, h5] at h2
      exact h2
    show (H.shift.edgeWalkup x).shift.shift = H.edgeWalkup x
    rw [← h3]
    exact (H.edgeWalkup x).shift_cycle

/-- `hypermap.hl`:3851 `lemma_degenerate_walkup_second_eq`。 -/
theorem degenerate_walkup_second_eq (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (h : H.DartDegenerate x) : H.faceWalkup x = H.edgeWalkup x := by
  rcases h with he | hn | hf
  · exact H.edge_degenerate_walkup_second_eq hx he
  · have h1 : (H.shift).edgeMap x = x := hn
    have h2 := (H.shift).edge_degenerate_walkup_third_eq hx h1
    have h3 : (H.shift.shift.edgeWalkup x).shift.shift = (H.edgeWalkup x).shift := by
      have h4 : (H.shift).faceWalkup x = (H.edgeWalkup x).shift := by
        show ((H.shift.shift.shift).edgeWalkup x).shift = _
        rw [H.shift_cycle]
      rw [h4] at h2
      exact h2
    show (H.shift.shift.edgeWalkup x).shift = H.edgeWalkup x
    have h5 := congrArg Hypermap.shift h3
    rw [(H.shift.shift.edgeWalkup x).shift_cycle] at h5
    rw [h5]
    exact (H.edgeWalkup x).shift_cycle
  · have h1 : (H.shift.shift).edgeMap x = x := hf
    have h2 := (H.shift.shift).edge_degenerate_walkup_first_eq hx h1
    have h3 : (H.edgeWalkup x).shift.shift = (H.shift.shift).edgeWalkup x := by
      have h4 : (H.shift.shift).nodeWalkup x = (H.edgeWalkup x).shift.shift := by
        show ((H.shift.shift.shift).edgeWalkup x).shift.shift = _
        rw [H.shift_cycle]
      rw [h4] at h2
      exact h2
    show (H.shift.shift.edgeWalkup x).shift = H.edgeWalkup x
    rw [← h3]
    exact (H.edgeWalkup x).shift_cycle

end Hypermap

/-- `s \ {x}` 的基数（`hypermap.hl`:3919 `CARD_MINUS_ONE` 的 `Set.ncard` 版）。 -/
theorem ncard_diff_singleton_mem {α : Type*} {s : Set α} {x : α} (hx : x ∈ s) (hf : s.Finite) :
    (s \ {x}).ncard = s.ncard - 1 := by
  have h1 : insert x (s \ {x}) = s := by
    ext y
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hy, -⟩)
      · exact hx
      · exact hy
    · intro hy
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨hy, hyx⟩
  have h2 := Set.ncard_insert_of_notMem (s := s \ {x}) (a := x) (by simp) hf.sdiff
  rw [h1] at h2
  omega

/-- `s \ {x, y}` 的基数（`hypermap.hl`:3932 `CARD_MINUS_DIFF_TWO_SET` 的 `Set.ncard` 版）。 -/
theorem ncard_diff_pair_mem {α : Type*} {s : Set α} {x y : α}
    (hxy : x ≠ y) (hx : x ∈ s) (hy : y ∈ s) (hf : s.Finite) :
    (s \ {x, y}).ncard = s.ncard - 2 := by
  have hsd : s \ {x, y} = (s \ {x}) \ {y} := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hym : y ∈ s \ {x} := Set.mem_sdiff_of_mem hy (by
    simp only [Set.mem_singleton_iff]
    exact fun h => hxy h.symm)
  rw [hsd, ncard_diff_singleton_mem hym hf.sdiff, ncard_diff_singleton_mem hx hf]
  have hsub : ({x, y} : Set α) ⊆ s := Set.pair_subset hx hy
  have h2 := Set.ncard_le_ncard hsub hf
  rw [Set.ncard_pair hxy] at h2
  omega

/-- 轨道是单点集则该点就是轨道的点（`hypermap.hl`:1044 `orbit_single_lemma` 的逆用）。 -/
theorem eq_of_orbit_eq_singleton {α : Type*} {f : Equiv.Perm α} {x y : α}
    (h : orbitMap f y = {x}) : y = x := by
  have h1 : y ∈ orbitMap f y := mem_orbitMap_self f y
  rw [h] at h1
  exact Set.mem_singleton_iff.mp h1

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `hypermap.hl`:3883 `component_at_isolated_dart`。 -/
theorem combComponent_eq_singleton_of_isolated (H : Hypermap α) (hx : H.IsolatedDart x) :
    H.combComponent x = {x} := by
  obtain ⟨he, hn, hf⟩ := hx
  ext y
  constructor
  · rintro ⟨p, n, hp0, hpn, hp⟩
    have key : ∀ i ≤ n, p i = x := by
      intro i
      induction i with
      | zero => intro _; exact hp0
      | succ k ih =>
        intro hkn
        have hk : p k = x := ih (Nat.le_of_succ_le hkn)
        rcases H.goOneStep_of_isPath hp hkn with h | h | h
        · rw [h, hk, he]
        · rw [h, hk, hn]
        · rw [h, hk, hf]
    rw [Set.mem_singleton_iff, ← hpn]
    exact key n le_rfl
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact H.mem_combComponent_self x

/-- `hypermap.hl`:3951 `NODE_NOT_EMPTY`（edge/face 版一并给出）。 -/
theorem one_le_edge_ncard (H : Hypermap α) (x : α) : 1 ≤ (H.edge x).ncard := by
  show 0 < (H.edge x).ncard
  rw [Set.ncard_pos (H.edge_finite x)]
  exact ⟨x, H.mem_edge_self x⟩

theorem one_le_node_ncard (H : Hypermap α) (x : α) : 1 ≤ (H.node x).ncard := by
  show 0 < (H.node x).ncard
  rw [Set.ncard_pos (H.node_finite x)]
  exact ⟨x, H.mem_node_self x⟩

theorem one_le_face_ncard (H : Hypermap α) (x : α) : 1 ≤ (H.face x).ncard := by
  show 0 < (H.face x).ncard
  rw [Set.ncard_pos (H.face_finite x)]
  exact ⟨x, H.mem_face_self x⟩

/-- `hypermap.hl`:3989 `WALKUP_EXCEPTION_COMPONENT`。 -/
theorem combComponent_walkup_singleton (H : Hypermap α) (x : α) :
    (H.edgeWalkup x).combComponent x = {x} :=
  (H.edgeWalkup x).combComponent_eq_singleton_of_isolated
    ⟨(H.edgeMap_walkup x x).1, (H.nodeMap_walkup x x).1, (H.faceMap_walkup x x).1⟩

/-- `hypermap.hl`:4003 `lemma_in_components`。 -/
theorem mem_darts_iff_combComponent_mem (H : Hypermap α) (x : α) :
    x ∈ H.darts ↔ H.combComponent x ∈ H.setOfComponents := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, h⟩
    have hsub := H.combComponent_subset_darts hy
    rw [h] at hsub
    exact hsub (H.mem_combComponent_self x)

/-- `hypermap.hl`:4019 `lemma_different_edges`。 -/
theorem edge_ne_of_not_mem (H : Hypermap α) (h : x ∉ H.edge y) : H.edge x ≠ H.edge y := by
  intro hcon
  exact h (hcon ▸ H.mem_edge_self x)

/-- `hypermap.hl`:4029 `lemma_different_nodes`。 -/
theorem node_ne_of_not_mem (H : Hypermap α) (h : x ∉ H.node y) : H.node x ≠ H.node y := by
  intro hcon
  exact h (hcon ▸ H.mem_node_self x)

/-- `hypermap.hl`:4039 `lemma_different_faces`。 -/
theorem face_ne_of_not_mem (H : Hypermap α) (h : x ∉ H.face y) : H.face x ≠ H.face y := by
  intro hcon
  exact h (hcon ▸ H.mem_face_self x)

/-- `hypermap.hl`:4053 `lemma_planar_index_on_walkup_at_isolated_dart`。 -/
theorem planarIndex_edgeWalkup_isolated (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hiso : H.IsolatedDart x) : H.planarIndex = (H.edgeWalkup x).planarIndex := by
  obtain ⟨he, hn, hf⟩ := hiso
  have he' : (H.edgeWalkup x).edgeMap x = x := (H.edgeMap_walkup x x).1
  have hn' : (H.edgeWalkup x).nodeMap x = x := (H.nodeMap_walkup x x).1
  have hf' : (H.edgeWalkup x).faceMap x = x := (H.faceMap_walkup x x).1
  -- X1: 边数
  have hX1 : H.numberOfEdges = (H.edgeWalkup x).numberOfEdges + 1 := by
    have hE1 : H.edge x = {x} := (orbitMap_singleton_iff H.edgeMap x).mpr he
    have hE2 : H.edge (H.nodeMap x) = {x} := by rw [hn]; exact hE1
    have hG2 : (H.edgeWalkup x).edge (H.nodeMap x) = {x} := by
      rw [hn]; exact (orbitMap_singleton_iff (H.edgeWalkup x).edgeMap x).mpr he'
    have hG3 : (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) = {x} := by
      have h3 : H.edgeMap⁻¹ x = x := (Perm_apply_eq_self_iff_symm _ _).mp he
      rw [h3]; exact (orbitMap_singleton_iff (H.edgeWalkup x).edgeMap x).mpr he'
    have hmem : ({x} : Set α) ∈ H.edgeSet := ⟨x, hx, hE1⟩
    have hnmem : ({x} : Set α) ∉ (H.edgeWalkup x).edgeSet := by
      rintro ⟨y, hy, hys⟩
      exact (Finset.mem_erase.mp hy).1 (eq_of_orbit_eq_singleton hys)
    have hdiff := H.edgeSet_walkup hx
    simp only [hE1, hE2, hG2, hG3, Set.pair_eq_singleton] at hdiff
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_singleton_mem hmem H.edgeSet_finite,
      Set.sdiff_singleton_eq_self hnmem] at hncard
    have hpos : 1 ≤ H.edgeSet.ncard := by
      show 0 < H.edgeSet.ncard
      rw [Set.ncard_pos H.edgeSet_finite]; exact ⟨{x}, hmem⟩
    unfold numberOfEdges
    omega
  -- X2: 节点数
  have hX2 : H.numberOfNodes = (H.edgeWalkup x).numberOfNodes + 1 := by
    have hE1 : H.node x = {x} := (orbitMap_singleton_iff H.nodeMap x).mpr hn
    have hG1 : (H.edgeWalkup x).node (H.nodeMap.symm x) = {x} := by
      have h3 : H.nodeMap.symm x = x := (Perm_apply_eq_self_iff_symm _ _).mp hn
      rw [h3]; exact (orbitMap_singleton_iff (H.edgeWalkup x).nodeMap x).mpr hn'
    have hmem : ({x} : Set α) ∈ H.nodeSet := ⟨x, hx, hE1⟩
    have hnmem : ({x} : Set α) ∉ (H.edgeWalkup x).nodeSet := by
      rintro ⟨y, hy, hys⟩
      exact (Finset.mem_erase.mp hy).1 (eq_of_orbit_eq_singleton hys)
    have hdiff := H.nodeSet_walkup hx
    simp only [hE1, hG1] at hdiff
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_singleton_mem hmem H.nodeSet_finite,
      Set.sdiff_singleton_eq_self hnmem] at hncard
    have hpos : 1 ≤ H.nodeSet.ncard := by
      show 0 < H.nodeSet.ncard
      rw [Set.ncard_pos H.nodeSet_finite]; exact ⟨{x}, hmem⟩
    unfold numberOfNodes
    omega
  -- X3: 面数
  have hX3 : H.numberOfFaces = (H.edgeWalkup x).numberOfFaces + 1 := by
    have hE1 : H.face x = {x} := (orbitMap_singleton_iff H.faceMap x).mpr hf
    have hG1 : (H.edgeWalkup x).face (H.faceMap.symm x) = {x} := by
      have h3 : H.faceMap.symm x = x := (Perm_apply_eq_self_iff_symm _ _).mp hf
      rw [h3]; exact (orbitMap_singleton_iff (H.edgeWalkup x).faceMap x).mpr hf'
    have hmem : ({x} : Set α) ∈ H.faceSet := ⟨x, hx, hE1⟩
    have hnmem : ({x} : Set α) ∉ (H.edgeWalkup x).faceSet := by
      rintro ⟨y, hy, hys⟩
      exact (Finset.mem_erase.mp hy).1 (eq_of_orbit_eq_singleton hys)
    have hdiff := H.faceSet_walkup hx
    simp only [hE1, hG1] at hdiff
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_singleton_mem hmem H.faceSet_finite,
      Set.sdiff_singleton_eq_self hnmem] at hncard
    have hpos : 1 ≤ H.faceSet.ncard := by
      show 0 < H.faceSet.ncard
      rw [Set.ncard_pos H.faceSet_finite]; exact ⟨{x}, hmem⟩
    unfold numberOfFaces
    omega
  -- X4: 组件数
  have hX4 : H.numberOfComponents = (H.edgeWalkup x).numberOfComponents + 1 := by
    have hC1 : H.combComponent x = {x} := H.combComponent_eq_singleton_of_isolated ⟨he, hn, hf⟩
    have hC3 : (H.edgeWalkup x).combComponent (H.nodeMap x) = {x} := by
      rw [hn]; exact H.combComponent_walkup_singleton x
    have hC4 : (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x) = {x} := by
      have h3 : H.edgeMap⁻¹ x = x := (Perm_apply_eq_self_iff_symm _ _).mp he
      rw [h3]; exact H.combComponent_walkup_singleton x
    have hmem : ({x} : Set α) ∈ H.setOfComponents := ⟨x, hx, hC1⟩
    have hnmem : ({x} : Set α) ∉ (H.edgeWalkup x).setOfComponents := by
      rintro ⟨y, hy, hys⟩
      have hyx : y = x := by
        have h1 : y ∈ (H.edgeWalkup x).combComponent y :=
          (H.edgeWalkup x).mem_combComponent_self y
        rw [hys] at h1
        exact Set.mem_singleton_iff.mp h1
      exact (Finset.mem_erase.mp hy).1 hyx
    have hdiff := H.setOfComponents_walkup hx
    simp only [hC1, hC3, hC4, Set.pair_eq_singleton] at hdiff
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_singleton_mem hmem H.setOfComponents_finite,
      Set.sdiff_singleton_eq_self hnmem] at hncard
    have hpos : 1 ≤ H.setOfComponents.ncard := by
      show 0 < H.setOfComponents.ncard
      rw [Set.ncard_pos H.setOfComponents_finite]; exact ⟨{x}, hmem⟩
    unfold numberOfComponents
    omega
  -- X5: dart 数
  have hX5 : H.darts.card = (H.edgeWalkup x).darts.card + 1 := by
    show H.darts.card = (H.darts.erase x).card + 1
    rw [Finset.card_erase_of_mem hx]
    have hpos : 0 < H.darts.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  unfold planarIndex
  rw [hX1, hX2, hX3, hX4, hX5]
  push_cast
  ring

/-- `hypermap.hl`:4228 `lemma_planar_index_on_walkup_at_edge_degenerate_dart`。 -/
theorem planarIndex_edgeWalkup_edge_degenerate (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hdeg : H.IsEdgeDegenerate x) : H.planarIndex = (H.edgeWalkup x).planarIndex := by
  obtain ⟨he, hn, hf⟩ := hdeg
  -- X1: 边数 `E_H = E_G + 1`
  have hX1 : H.numberOfEdges = (H.edgeWalkup x).numberOfEdges + 1 := by
    have hE1 : H.edge x = {x} := (orbitMap_singleton_iff H.edgeMap x).mpr he
    have hG1 : (H.edgeWalkup x).edge x = {x} :=
      (orbitMap_singleton_iff (H.edgeWalkup x).edgeMap x).mpr (H.edgeMap_walkup x x).1
    have hEne1 : H.edge (H.nodeMap x) ≠ ({x} : Set α) := by
      intro hcon
      exact hn (eq_of_orbit_eq_singleton hcon)
    have hGne1 : (H.edgeWalkup x).edge (H.nodeMap x) ≠ ({x} : Set α) := by
      intro hcon
      exact hn (eq_of_orbit_eq_singleton hcon)
    have hE2 : H.edgeMap⁻¹ x = x := (Perm_apply_eq_self_iff_symm _ _).mp he
    have hG3 : (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) = {x} := by
      rw [hE2]; exact hG1
    have hmem1 : ({x} : Set α) ∈ H.edgeSet := ⟨x, hx, hE1⟩
    have hmem2 : H.edge (H.nodeMap x) ∈ H.edgeSet :=
      ⟨H.nodeMap x, H.nodeMap_apply_mem hx, rfl⟩
    have hnmem : ({x} : Set α) ∉ (H.edgeWalkup x).edgeSet := by
      rintro ⟨y, hy, hys⟩
      exact (Finset.mem_erase.mp hy).1 (eq_of_orbit_eq_singleton hys)
    have hGmem2 : (H.edgeWalkup x).edge (H.nodeMap x) ∈ (H.edgeWalkup x).edgeSet :=
      ⟨H.nodeMap x, (H.nodeMap_walkup_mem_darts hx hn).1, rfl⟩
    have hdiff := H.edgeSet_walkup hx
    rw [hE1, hG3] at hdiff
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_pair_mem hEne1.symm hmem1 hmem2 H.edgeSet_finite,
      show (H.edgeWalkup x).edgeSet \ {(H.edgeWalkup x).edge (H.nodeMap x), {x}} =
        ((H.edgeWalkup x).edgeSet \ {{x}}) \ {(H.edgeWalkup x).edge (H.nodeMap x)} from by
        ext u
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto,
      Set.sdiff_singleton_eq_self hnmem,
      ncard_diff_singleton_mem hGmem2 (H.edgeWalkup x).edgeSet_finite] at hncard
    have hpos : 2 ≤ H.edgeSet.ncard := by
      have hsub : ({{x}, H.edge (H.nodeMap x)} : Set (Set α)) ⊆ H.edgeSet :=
        Set.pair_subset hmem1 hmem2
      have h2 := Set.ncard_le_ncard hsub H.edgeSet_finite
      rwa [Set.ncard_pair hEne1.symm] at h2
    have hpos2 : 1 ≤ (H.edgeWalkup x).edgeSet.ncard := by
      show 0 < (H.edgeWalkup x).edgeSet.ncard
      rw [Set.ncard_pos (H.edgeWalkup x).edgeSet_finite]
      exact ⟨(H.edgeWalkup x).edge (H.nodeMap x), hGmem2⟩
    unfold numberOfEdges
    omega
  -- X2: 节点数不变
  have hX2 : H.numberOfNodes = (H.edgeWalkup x).numberOfNodes := by
    have hdiff := H.nodeSet_walkup hx
    have hmem1 : H.node x ∈ H.nodeSet := ⟨x, hx, rfl⟩
    have hmem2 : (H.edgeWalkup x).node (H.nodeMap.symm x) ∈ (H.edgeWalkup x).nodeSet :=
      ⟨H.nodeMap.symm x, (H.nodeMap_walkup_mem_darts hx hn).2, rfl⟩
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_singleton_mem hmem1 H.nodeSet_finite,
      ncard_diff_singleton_mem hmem2 (H.edgeWalkup x).nodeSet_finite] at hncard
    have hpos1 : 1 ≤ H.nodeSet.ncard := by
      show 0 < H.nodeSet.ncard
      rw [Set.ncard_pos H.nodeSet_finite]; exact ⟨H.node x, hmem1⟩
    have hpos2 : 1 ≤ (H.edgeWalkup x).nodeSet.ncard := by
      show 0 < (H.edgeWalkup x).nodeSet.ncard
      rw [Set.ncard_pos (H.edgeWalkup x).nodeSet_finite]
      exact ⟨(H.edgeWalkup x).node (H.nodeMap.symm x), hmem2⟩
    unfold numberOfNodes
    omega
  -- X4: 面数不变
  have hX4 : H.numberOfFaces = (H.edgeWalkup x).numberOfFaces := by
    have hdiff := H.faceSet_walkup hx
    have hmem1 : H.face x ∈ H.faceSet := ⟨x, hx, rfl⟩
    have hmem2 : (H.edgeWalkup x).face (H.faceMap.symm x) ∈ (H.edgeWalkup x).faceSet :=
      ⟨H.faceMap.symm x, (H.faceMap_walkup_mem_darts hx hf).2, rfl⟩
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_singleton_mem hmem1 H.faceSet_finite,
      ncard_diff_singleton_mem hmem2 (H.edgeWalkup x).faceSet_finite] at hncard
    have hpos1 : 1 ≤ H.faceSet.ncard := by
      show 0 < H.faceSet.ncard
      rw [Set.ncard_pos H.faceSet_finite]; exact ⟨H.face x, hmem1⟩
    have hpos2 : 1 ≤ (H.edgeWalkup x).faceSet.ncard := by
      show 0 < (H.edgeWalkup x).faceSet.ncard
      rw [Set.ncard_pos (H.edgeWalkup x).faceSet_finite]
      exact ⟨(H.edgeWalkup x).face (H.faceMap.symm x), hmem2⟩
    unfold numberOfFaces
    omega
  -- X5: 组件数不变
  have hX5 : H.numberOfComponents = (H.edgeWalkup x).numberOfComponents := by
    have hdiff := H.setOfComponents_walkup hx
    have hG1 : (H.edgeWalkup x).combComponent x = {x} := H.combComponent_walkup_singleton x
    have hG3 : (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x) = {x} := by
      have hE2 : H.edgeMap⁻¹ x = x := (Perm_apply_eq_self_iff_symm _ _).mp he
      rw [hE2]; exact hG1
    have hnmem : ({x} : Set α) ∉ (H.edgeWalkup x).setOfComponents := by
      rintro ⟨y, hy, hys⟩
      have hyx : y = x := by
        have h1 : y ∈ (H.edgeWalkup x).combComponent y :=
          (H.edgeWalkup x).mem_combComponent_self y
        rw [hys] at h1
        exact Set.mem_singleton_iff.mp h1
      exact (Finset.mem_erase.mp hy).1 hyx
    have hGne2 : (H.edgeWalkup x).combComponent (H.nodeMap x) ≠ ({x} : Set α) := by
      intro hcon
      apply hn
      have h1 : H.nodeMap x ∈ (H.edgeWalkup x).combComponent (H.nodeMap x) :=
        (H.edgeWalkup x).mem_combComponent_self _
      rw [hcon] at h1
      exact Set.mem_singleton_iff.mp h1
    have hmem1 : H.combComponent x ∈ H.setOfComponents := ⟨x, hx, rfl⟩
    have hGmem2 : (H.edgeWalkup x).combComponent (H.nodeMap x) ∈
        (H.edgeWalkup x).setOfComponents :=
      ⟨H.nodeMap x, (H.nodeMap_walkup_mem_darts hx hn).1, rfl⟩
    rw [hG3] at hdiff
    have hncard := congrArg Set.ncard hdiff
    rw [ncard_diff_singleton_mem hmem1 H.setOfComponents_finite,
      show (H.edgeWalkup x).setOfComponents \
          {(H.edgeWalkup x).combComponent (H.nodeMap x), {x}} =
        ((H.edgeWalkup x).setOfComponents \ {{x}}) \
          {(H.edgeWalkup x).combComponent (H.nodeMap x)} from by
        ext u
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto,
      Set.sdiff_singleton_eq_self hnmem,
      ncard_diff_singleton_mem hGmem2 (H.edgeWalkup x).setOfComponents_finite] at hncard
    have hpos1 : 1 ≤ H.setOfComponents.ncard := by
      show 0 < H.setOfComponents.ncard
      rw [Set.ncard_pos H.setOfComponents_finite]; exact ⟨H.combComponent x, hmem1⟩
    have hpos2 : 1 ≤ (H.edgeWalkup x).setOfComponents.ncard := by
      show 0 < (H.edgeWalkup x).setOfComponents.ncard
      rw [Set.ncard_pos (H.edgeWalkup x).setOfComponents_finite]
      exact ⟨(H.edgeWalkup x).combComponent (H.nodeMap x), hGmem2⟩
    unfold numberOfComponents
    omega
  -- X6: dart 数
  have hX6 : H.darts.card = (H.edgeWalkup x).darts.card + 1 := by
    show H.darts.card = (H.darts.erase x).card + 1
    rw [Finset.card_erase_of_mem hx]
    have hpos : 0 < H.darts.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  unfold planarIndex
  rw [hX1, hX2, hX4, hX5, hX6]
  push_cast
  ring

/-- `hypermap.hl`:4398 `lemma_planar_index_on_walkup_at_degenerate_dart`。 -/
theorem planarIndex_edgeWalkup_degenerate (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hdeg : H.DartDegenerate x) : H.planarIndex = (H.edgeWalkup x).planarIndex := by
  rw [H.dartDegenerate_iff] at hdeg
  rcases hdeg with hiso | hedeg | hndeg | hfdeg
  · exact H.planarIndex_edgeWalkup_isolated hx hiso
  · exact H.planarIndex_edgeWalkup_edge_degenerate hx hedeg
  · -- node 退化：经 shift 归约到 edge 退化
    obtain ⟨he, hn, hf⟩ := hndeg
    have hdeg' : (H.shift).IsEdgeDegenerate x := ⟨hn, hf, he⟩
    have h1 := (H.shift).planarIndex_edgeWalkup_edge_degenerate hx hdeg'
    have h2 : (H.shift).planarIndex = H.planarIndex := H.planarIndex_shift.symm
    have h3 : ((H.shift).edgeWalkup x).planarIndex = (H.nodeWalkup x).planarIndex := by
      show ((H.shift).edgeWalkup x).planarIndex =
        (((H.shift).edgeWalkup x).shift.shift).planarIndex
      rw [← ((H.shift).edgeWalkup x).shift.planarIndex_shift]
      exact ((H.shift).edgeWalkup x).planarIndex_shift
    have h4 : H.nodeWalkup x = H.edgeWalkup x :=
      H.degenerate_walkup_first_eq hx ((H.dartDegenerate_iff x).mpr (Or.inr (Or.inr (Or.inl ⟨he, hn, hf⟩))))
    rw [← h2, h1, h3, h4]
  · -- face 退化：经 shift² 归约
    obtain ⟨he, hn, hf⟩ := hfdeg
    have hdeg' : (H.shift.shift).IsEdgeDegenerate x := ⟨hf, he, hn⟩
    have h1 := (H.shift.shift).planarIndex_edgeWalkup_edge_degenerate hx hdeg'
    have h2 : (H.shift.shift).planarIndex = H.planarIndex :=
      (H.shift.planarIndex_shift).symm.trans H.planarIndex_shift.symm
    have h3 : ((H.shift.shift).edgeWalkup x).planarIndex = (H.faceWalkup x).planarIndex :=
      ((H.shift.shift).edgeWalkup x).planarIndex_shift
    have h4 : H.faceWalkup x = H.edgeWalkup x :=
      H.degenerate_walkup_second_eq hx ((H.dartDegenerate_iff x).mpr (Or.inr (Or.inr (Or.inr ⟨he, hn, hf⟩))))
    rw [← h2, h1, h3, h4]

/-- `hypermap.hl`:4432 `lemma_card_walkup_dart`。 -/
theorem card_walkup_dart (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.darts.card = (H.edgeWalkup x).darts.card + 1 := by
  show H.darts.card = (H.darts.erase x).card + 1
  rw [Finset.card_erase_of_mem hx]
  have hpos : 0 < H.darts.card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- `hypermap.hl`:4440 `lemma_splitting_case_count_edges`。 -/
theorem splitting_case_count_edges (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hsplit : H.IsEdgeSplit x) : H.numberOfEdges + 1 = (H.edgeWalkup x).numberOfEdges := by
  obtain ⟨hnd, hnx⟩ := hsplit
  have hmem1 : H.edge x ∈ H.edgeSet := ⟨x, hx, rfl⟩
  have hid : H.edge (H.nodeMap x) = H.edge x := (H.edge_eq_of_mem hnx).symm
  have hpart3 : (H.edgeWalkup x).edgeMap (H.edgeMap⁻¹ x) = H.faceMap⁻¹ x :=
    (H.edgeMap_walkup x x).2.2.1
      ⟨(Perm_apply_ne_self_iff_symm _ _).mp hnd.2.2,
        (Perm_apply_ne_self_iff_symm _ _).mp hnd.1⟩
  have hmem_f : H.faceMap⁻¹ x ∈ (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) := by
    have h1 := (H.edgeWalkup x).pow_edgeMap_mem_edge (H.edgeMap⁻¹ x) 1
    rw [pow_one, hpart3] at h1
    exact h1
  have hid2 : (H.edgeWalkup x).edge (H.faceMap⁻¹ x) = (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) :=
    ((H.edgeWalkup x).edge_eq_of_mem hmem_f).symm
  have hne : (H.edgeWalkup x).edge (H.nodeMap x) ≠ (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) := by
    intro hcon
    have h1 := (H.edge_split hx ⟨hnd, hnx⟩).1
    apply h1
    have h2 : H.faceMap⁻¹ x ∈ (H.edgeWalkup x).edge (H.faceMap⁻¹ x) :=
      (H.edgeWalkup x).mem_edge_self _
    rwa [hid2, ← hcon] at h2
  have hGmem1 : (H.edgeWalkup x).edge (H.nodeMap x) ∈ (H.edgeWalkup x).edgeSet :=
    ⟨H.nodeMap x, (H.nodeMap_walkup_mem_darts hx hnd.2.1).1, rfl⟩
  have hGmem2 : (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) ∈ (H.edgeWalkup x).edgeSet :=
    ⟨H.edgeMap⁻¹ x, (H.edgeMap_walkup_mem_darts hx hnd.1).2, rfl⟩
  have hdiff := H.edgeSet_walkup hx
  rw [hid, Set.pair_eq_singleton] at hdiff
  have hncard := congrArg Set.ncard hdiff
  rw [ncard_diff_singleton_mem hmem1 H.edgeSet_finite,
    ncard_diff_pair_mem hne hGmem1 hGmem2 (H.edgeWalkup x).edgeSet_finite] at hncard
  have hpos1 : 1 ≤ H.edgeSet.ncard := by
    show 0 < H.edgeSet.ncard
    rw [Set.ncard_pos H.edgeSet_finite]; exact ⟨H.edge x, hmem1⟩
  have hpos2 : 2 ≤ (H.edgeWalkup x).edgeSet.ncard := by
    have hsub : ({(H.edgeWalkup x).edge (H.nodeMap x), (H.edgeWalkup x).edge (H.edgeMap⁻¹ x)} :
        Set (Set α)) ⊆ (H.edgeWalkup x).edgeSet := Set.pair_subset hGmem1 hGmem2
    have h2 := Set.ncard_le_ncard hsub (H.edgeWalkup x).edgeSet_finite
    rwa [Set.ncard_pair hne] at h2
  unfold numberOfEdges
  omega

/-- `hypermap.hl`:4491 `lemma_merge_case_count_edges`。 -/
theorem merge_case_count_edges (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hmerge : H.IsEdgeMerge x) : H.numberOfEdges = (H.edgeWalkup x).numberOfEdges + 1 := by
  obtain ⟨hnd, hnx⟩ := hmerge
  have hne : H.edge x ≠ H.edge (H.nodeMap x) := (H.edge_ne_of_not_mem hnx).symm
  have hmem1 : H.edge x ∈ H.edgeSet := ⟨x, hx, rfl⟩
  have hmem2 : H.edge (H.nodeMap x) ∈ H.edgeSet := ⟨H.nodeMap x, H.nodeMap_apply_mem hx, rfl⟩
  have hinv : H.edgeMap⁻¹ x ∈ H.edge x := H.edgeMap_permutes.symm_apply_mem_orbitMap x
  have hme := H.edge_merge hx ⟨hnd, hnx⟩
  have hid : (H.edgeWalkup x).edge (H.edgeMap⁻¹ x) = (H.edgeWalkup x).edge (H.nodeMap x) := by
    have h1 : H.edgeMap⁻¹ x ∈ ({x} ∪ (H.edgeWalkup x).edge (H.nodeMap x) : Set α) := by
      rw [hme]; exact Set.mem_union_left _ hinv
    rcases h1 with h2 | h2
    · exfalso
      exact (Perm_apply_ne_self_iff_symm _ _).mp hnd.1 (Set.mem_singleton_iff.mp h2)
    · exact ((H.edgeWalkup x).edge_eq_of_mem h2).symm
  have hGmem1 : (H.edgeWalkup x).edge (H.nodeMap x) ∈ (H.edgeWalkup x).edgeSet :=
    ⟨H.nodeMap x, (H.nodeMap_walkup_mem_darts hx hnd.2.1).1, rfl⟩
  have hdiff := H.edgeSet_walkup hx
  rw [hid, Set.pair_eq_singleton] at hdiff
  have hncard := congrArg Set.ncard hdiff
  rw [ncard_diff_pair_mem hne hmem1 hmem2 H.edgeSet_finite,
    ncard_diff_singleton_mem hGmem1 (H.edgeWalkup x).edgeSet_finite] at hncard
  have hpos1 : 2 ≤ H.edgeSet.ncard := by
    have hsub : ({H.edge x, H.edge (H.nodeMap x)} : Set (Set α)) ⊆ H.edgeSet :=
      Set.pair_subset hmem1 hmem2
    have h2 := Set.ncard_le_ncard hsub H.edgeSet_finite
    rwa [Set.ncard_pair hne] at h2
  have hpos2 : 1 ≤ (H.edgeWalkup x).edgeSet.ncard := by
    show 0 < (H.edgeWalkup x).edgeSet.ncard
    rw [Set.ncard_pos (H.edgeWalkup x).edgeSet_finite]
    exact ⟨(H.edgeWalkup x).edge (H.nodeMap x), hGmem1⟩
  unfold numberOfEdges
  omega

/-- `hypermap.hl`:4540 `lemma_walkup_count_nodes`。 -/
theorem walkup_count_nodes (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hnd : H.DartNondegenerate x) : H.numberOfNodes = (H.edgeWalkup x).numberOfNodes := by
  have hdiff := H.nodeSet_walkup hx
  have hmem1 : H.node x ∈ H.nodeSet := ⟨x, hx, rfl⟩
  have hmem2 : (H.edgeWalkup x).node (H.nodeMap.symm x) ∈ (H.edgeWalkup x).nodeSet :=
    ⟨H.nodeMap.symm x, (H.nodeMap_walkup_mem_darts hx hnd.2.1).2, rfl⟩
  have hncard := congrArg Set.ncard hdiff
  rw [ncard_diff_singleton_mem hmem1 H.nodeSet_finite,
    ncard_diff_singleton_mem hmem2 (H.edgeWalkup x).nodeSet_finite] at hncard
  have hpos1 : 1 ≤ H.nodeSet.ncard := by
    show 0 < H.nodeSet.ncard
    rw [Set.ncard_pos H.nodeSet_finite]; exact ⟨H.node x, hmem1⟩
  have hpos2 : 1 ≤ (H.edgeWalkup x).nodeSet.ncard := by
    show 0 < (H.edgeWalkup x).nodeSet.ncard
    rw [Set.ncard_pos (H.edgeWalkup x).nodeSet_finite]
    exact ⟨(H.edgeWalkup x).node (H.nodeMap.symm x), hmem2⟩
  unfold numberOfNodes
  omega

/-- `hypermap.hl`:4563 `lemma_walkup_count_faces`。 -/
theorem walkup_count_faces (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hnd : H.DartNondegenerate x) : H.numberOfFaces = (H.edgeWalkup x).numberOfFaces := by
  have hdiff := H.faceSet_walkup hx
  have hmem1 : H.face x ∈ H.faceSet := ⟨x, hx, rfl⟩
  have hmem2 : (H.edgeWalkup x).face (H.faceMap.symm x) ∈ (H.edgeWalkup x).faceSet :=
    ⟨H.faceMap.symm x, (H.faceMap_walkup_mem_darts hx hnd.2.2).2, rfl⟩
  have hncard := congrArg Set.ncard hdiff
  rw [ncard_diff_singleton_mem hmem1 H.faceSet_finite,
    ncard_diff_singleton_mem hmem2 (H.edgeWalkup x).faceSet_finite] at hncard
  have hpos1 : 1 ≤ H.faceSet.ncard := by
    show 0 < H.faceSet.ncard
    rw [Set.ncard_pos H.faceSet_finite]; exact ⟨H.face x, hmem1⟩
  have hpos2 : 1 ≤ (H.edgeWalkup x).faceSet.ncard := by
    show 0 < (H.edgeWalkup x).faceSet.ncard
    rw [Set.ncard_pos (H.edgeWalkup x).faceSet_finite]
    exact ⟨(H.edgeWalkup x).face (H.faceMap.symm x), hmem2⟩
  unfold numberOfFaces
  omega

/-- `hypermap.hl`:4589 `lemma_walkup_count_splitting_components`。 -/
theorem walkup_count_splitting_components (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hnd : H.DartNondegenerate x)
    (hsplit : (H.edgeWalkup x).combComponent (H.nodeMap x) ≠
      (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x)) :
    H.numberOfComponents + 1 = (H.edgeWalkup x).numberOfComponents := by
  have hdiff := H.setOfComponents_walkup hx
  have hmem1 : H.combComponent x ∈ H.setOfComponents := ⟨x, hx, rfl⟩
  have hGmem1 : (H.edgeWalkup x).combComponent (H.nodeMap x) ∈
      (H.edgeWalkup x).setOfComponents :=
    ⟨H.nodeMap x, (H.nodeMap_walkup_mem_darts hx hnd.2.1).1, rfl⟩
  have hGmem2 : (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x) ∈
      (H.edgeWalkup x).setOfComponents :=
    ⟨H.edgeMap⁻¹ x, (H.edgeMap_walkup_mem_darts hx hnd.1).2, rfl⟩
  have hncard := congrArg Set.ncard hdiff
  rw [ncard_diff_singleton_mem hmem1 H.setOfComponents_finite,
    ncard_diff_pair_mem hsplit hGmem1 hGmem2 (H.edgeWalkup x).setOfComponents_finite] at hncard
  have hpos1 : 1 ≤ H.setOfComponents.ncard := by
    show 0 < H.setOfComponents.ncard
    rw [Set.ncard_pos H.setOfComponents_finite]; exact ⟨H.combComponent x, hmem1⟩
  have hpos2 : 2 ≤ (H.edgeWalkup x).setOfComponents.ncard := by
    have hsub : ({(H.edgeWalkup x).combComponent (H.nodeMap x),
        (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x)} : Set (Set α)) ⊆
        (H.edgeWalkup x).setOfComponents := Set.pair_subset hGmem1 hGmem2
    have h2 := Set.ncard_le_ncard hsub (H.edgeWalkup x).setOfComponents_finite
    rwa [Set.ncard_pair hsplit] at h2
  unfold numberOfComponents
  omega

/-- `hypermap.hl`:4616 `lemma_walkup_count_not_splitting_components`。 -/
theorem walkup_count_not_splitting_components (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hnd : H.DartNondegenerate x)
    (hnsplit : (H.edgeWalkup x).combComponent (H.nodeMap x) =
      (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x)) :
    H.numberOfComponents = (H.edgeWalkup x).numberOfComponents := by
  have hdiff := H.setOfComponents_walkup hx
  rw [hnsplit, Set.pair_eq_singleton] at hdiff
  have hmem1 : H.combComponent x ∈ H.setOfComponents := ⟨x, hx, rfl⟩
  have hGmem1 : (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x) ∈
      (H.edgeWalkup x).setOfComponents :=
    ⟨H.edgeMap⁻¹ x, (H.edgeMap_walkup_mem_darts hx hnd.1).2, rfl⟩
  have hncard := congrArg Set.ncard hdiff
  rw [ncard_diff_singleton_mem hmem1 H.setOfComponents_finite,
    ncard_diff_singleton_mem hGmem1 (H.edgeWalkup x).setOfComponents_finite] at hncard
  have hpos1 : 1 ≤ H.setOfComponents.ncard := by
    show 0 < H.setOfComponents.ncard
    rw [Set.ncard_pos H.setOfComponents_finite]; exact ⟨H.combComponent x, hmem1⟩
  have hpos2 : 1 ≤ (H.edgeWalkup x).setOfComponents.ncard := by
    show 0 < (H.edgeWalkup x).setOfComponents.ncard
    rw [Set.ncard_pos (H.edgeWalkup x).setOfComponents_finite]
    exact ⟨(H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x), hGmem1⟩
  unfold numberOfComponents
  omega

/-- `hypermap.hl`:4639 `is_splitting_component`。 -/
def IsSplittingComponent (H : Hypermap α) (x : α) : Prop :=
  (H.edgeWalkup x).combComponent (H.nodeMap x) ≠ (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x)

/-- merge 情形下两个接缝组件相等（`hypermap.hl`:4641 证明中的 `J1`）。 -/
theorem merge_combComponent_eq (H : Hypermap α) {x : α} (hx : x ∈ H.darts)
    (hmerge : H.IsEdgeMerge x) :
    (H.edgeWalkup x).combComponent (H.nodeMap x) =
      (H.edgeWalkup x).combComponent (H.edgeMap⁻¹ x) := by
  obtain ⟨hnd, hnx⟩ := hmerge
  have hinv : H.edgeMap⁻¹ x ∈ H.edge x := H.edgeMap_permutes.symm_apply_mem_orbitMap x
  have hme := H.edge_merge hx ⟨hnd, hnx⟩
  have h1 : H.edgeMap⁻¹ x ∈ ({x} ∪ (H.edgeWalkup x).edge (H.nodeMap x) : Set α) := by
    rw [hme]; exact Set.mem_union_left _ hinv
  rcases h1 with h2 | h2
  · exfalso
    exact (Perm_apply_ne_self_iff_symm _ _).mp hnd.1 (Set.mem_singleton_iff.mp h2)
  · have h3 : H.edgeMap⁻¹ x ∈ (H.edgeWalkup x).combComponent (H.nodeMap x) :=
      (H.edgeWalkup x).edge_subset_component _ h2
    exact (H.edgeWalkup x).combComponent_eq_of_mem h3

/-- `hypermap.hl`:4641 `lemma_planar_index_on_nondegenerate`。 -/
theorem planarIndex_edgeWalkup_nondegenerate (H : Hypermap α) {x : α}
    (hx : x ∈ H.darts) (hnd : H.DartNondegenerate x) :
    (H.IsEdgeSplit x ∧ ¬ H.IsSplittingComponent x →
      H.planarIndex + 2 = (H.edgeWalkup x).planarIndex) ∧
    (¬(H.IsEdgeSplit x ∧ ¬ H.IsSplittingComponent x) →
      H.planarIndex = (H.edgeWalkup x).planarIndex) := by
  have hN := H.walkup_count_nodes hx hnd
  have hF := H.walkup_count_faces hx hnd
  have hD := H.card_walkup_dart hx
  constructor
  · intro ⟨hsplit, hnsplit⟩
    have hE := H.splitting_case_count_edges hx hsplit
    have hC := H.walkup_count_not_splitting_components hx hnd (not_not.mp hnsplit)
    unfold planarIndex
    omega
  · intro h
    by_cases hsplit : H.IsEdgeSplit x
    · have hsc : H.IsSplittingComponent x := by
        by_contra hcon
        exact h ⟨hsplit, hcon⟩
      have hE := H.splitting_case_count_edges hx hsplit
      have hC := H.walkup_count_splitting_components hx hnd hsc
      unfold planarIndex
      omega
    · have hmerge : H.IsEdgeMerge x := ⟨hnd, fun hcon => hsplit ⟨hnd, hcon⟩⟩
      have hE := H.merge_case_count_edges hx hmerge
      have hC := H.walkup_count_not_splitting_components hx hnd
        (H.merge_combComponent_eq hx hmerge)
      unfold planarIndex
      omega

/-- `hypermap.hl`:4705 `lemma_desc_planar_index`。 -/
theorem planarIndex_le_edgeWalkup (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.planarIndex ≤ (H.edgeWalkup x).planarIndex := by
  rcases H.dartNondegenerate_or_dartDegenerate x with hnd | hdeg
  · obtain ⟨h1, h2⟩ := H.planarIndex_edgeWalkup_nondegenerate hx hnd
    by_cases h : H.IsEdgeSplit x ∧ ¬ H.IsSplittingComponent x
    · have h3 := h1 h
      omega
    · have h3 := h2 h
      omega
  · have h3 := H.planarIndex_edgeWalkup_degenerate hx hdeg
    omega

/-- `hypermap.hl`:4721 `lemmaBISHKQW`。 -/
theorem planarIndex_le_walkups (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.planarIndex ≤ (H.edgeWalkup x).planarIndex ∧
      H.planarIndex ≤ (H.nodeWalkup x).planarIndex ∧
        H.planarIndex ≤ (H.faceWalkup x).planarIndex := by
  refine ⟨H.planarIndex_le_edgeWalkup hx, ?_, ?_⟩
  · have h1 : (H.shift).planarIndex ≤ ((H.shift).edgeWalkup x).planarIndex :=
      (H.shift).planarIndex_le_edgeWalkup hx
    rw [← H.planarIndex_shift] at h1
    have h2 : ((H.shift).edgeWalkup x).planarIndex = (H.nodeWalkup x).planarIndex := by
      show ((H.shift).edgeWalkup x).planarIndex =
        (((H.shift).edgeWalkup x).shift.shift).planarIndex
      rw [← ((H.shift).edgeWalkup x).shift.planarIndex_shift]
      exact ((H.shift).edgeWalkup x).planarIndex_shift
    rwa [h2] at h1
  · have h1 : (H.shift.shift).planarIndex ≤ ((H.shift.shift).edgeWalkup x).planarIndex :=
      (H.shift.shift).planarIndex_le_edgeWalkup hx
    have h2 : H.planarIndex = (H.shift.shift).planarIndex :=
      H.planarIndex_shift.trans (H.shift.planarIndex_shift)
    rw [← h2] at h1
    have h3 : ((H.shift.shift).edgeWalkup x).planarIndex = (H.faceWalkup x).planarIndex :=
      ((H.shift.shift).edgeWalkup x).planarIndex_shift
    rwa [h3] at h1

/-- `hypermap.hl`:4741 `lemmaFOAGLPA`（Euler 主定理：`planar_index ≤ 0`）。 -/
theorem planarIndex_le_zero (H : Hypermap α) : H.planarIndex ≤ 0 := by
  have key : ∀ n : ℕ, ∀ H : Hypermap α, H.darts.card ≤ n → H.planarIndex ≤ 0 := by
    intro n
    induction n with
    | zero =>
      intro H h
      have h0 : H.darts.card = 0 := by omega
      rw [H.planarIndex_eq_zero_of_darts_card_eq_zero h0]
    | succ n ihn =>
      intro H h
      by_cases hd : H.darts = ∅
      · rw [H.planarIndex_eq_zero_of_darts_card_eq_zero (Finset.card_eq_zero.mpr hd)]
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hd
        have h1 := H.planarIndex_le_edgeWalkup hx
        have h2 : (H.edgeWalkup x).planarIndex ≤ 0 := by
          apply ihn
          show (H.darts.erase x).card ≤ n
          rw [Finset.card_erase_of_mem hx]
          omega
        omega
  exact key H.darts.card H le_rfl

/-- `hypermap.hl`:4771 `lemmaSGCOSXK`。 -/
theorem planar_walkup (H : Hypermap α) {x : α} (hx : x ∈ H.darts) (hplanar : H.Planar) :
    (H.edgeWalkup x).Planar ∧ (H.nodeWalkup x).Planar ∧ (H.faceWalkup x).Planar := by
  rw [H.planar_iff_planarIndex_eq_zero] at hplanar
  obtain ⟨hE, hN, hF⟩ := H.planarIndex_le_walkups hx
  have h1 := (H.edgeWalkup x).planarIndex_le_zero
  have h2 := (H.nodeWalkup x).planarIndex_le_zero
  have h3 := (H.faceWalkup x).planarIndex_le_zero
  refine ⟨?_, ?_, ?_⟩ <;> rw [planar_iff_planarIndex_eq_zero] <;> omega

end Hypermap

/-! ## Convolution（`hypermap.hl`:4793–4935） -/

/-- `hypermap.hl`:4793 `convolution_rep`。 -/
theorem mul_self_eq_one_iff_eq_inv {α : Type*} (p : Equiv.Perm α) :
    p * p = 1 ↔ p = p⁻¹ := by
  constructor
  · intro h; exact eq_inv_of_mul_eq_one_left h
  · intro h; nth_rewrite 1 [h]; exact inv_mul_cancel p

/-- `hypermap.hl`:4801 `convolution_inv`。 -/
theorem mul_self_eq_one_iff_inv_mul_self {α : Type*} (p : Equiv.Perm α) :
    p * p = 1 ↔ p⁻¹ * p⁻¹ = 1 := by
  constructor
  · intro h
    rw [← mul_inv_rev, h, inv_one]
  · intro h
    have h2 : p * p = (p⁻¹ * p⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [h2, h, inv_one]

/-- `hypermap.hl`:4816 `convolution_belong`。 -/
theorem PermutesOn.mul_self_eq_one_iff {α : Type*} {p : Equiv.Perm α} {s : Finset α}
    (hp : PermutesOn p s) : p * p = 1 ↔ ∀ x ∈ s, p (p x) = x := by
  constructor
  · intro h x _
    have : (p * p) x = (1 : Equiv.Perm α) x := by rw [h]
    rwa [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this
  · intro h
    ext x
    by_cases hx : x ∈ s
    · rw [Equiv.Perm.mul_apply, h x hx, Equiv.Perm.one_apply]
    · rw [Equiv.Perm.mul_apply, hp x hx, hp x hx, Equiv.Perm.one_apply]

namespace Hypermap

variable {α : Type*} [DecidableEq α] {x y z : α}

/-- `hypermap.hl`:4834 `edge_convolution`。 -/
theorem plain_iff_node_face_mul_apply (H : Hypermap α) :
    H.Plain ↔ ∀ x ∈ H.darts, H.nodeMap (H.faceMap (H.nodeMap (H.faceMap x))) = x := by
  unfold Plain
  rw [mul_self_eq_one_iff_inv_mul_self]
  have h1 : H.edgeMap⁻¹ = H.nodeMap * H.faceMap := H.inverse_hypermap_maps.1
  rw [h1, PermutesOn.mul_self_eq_one_iff (H.nodeMap_permutes.mul H.faceMap_permutes)]
  exact forall_congr' fun x => forall_congr' fun _ => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

/-- `hypermap.hl`:4843 `edge_map_convolution`。 -/
theorem plain_iff_edgeMap_eq (H : Hypermap α) :
    H.Plain ↔ H.edgeMap = H.nodeMap * H.faceMap := by
  unfold Plain
  rw [mul_self_eq_one_iff_eq_inv, H.inverse_hypermap_maps.1]

/-- `hypermap.hl`:4850 `lemma_convolution_evaluation`。 -/
theorem PermutesOn.apply_apply_self_iff_ncard_le_two {α : Type*} {p : Equiv.Perm α} {s : Finset α}
    {x : α} (hp : PermutesOn p s) : p (p x) = x ↔ (orbitMap p x).ncard ≤ 2 := by
  constructor
  · intro h
    have h2 : (p ^ 2) x = x := by
      rw [pow_two, Equiv.Perm.mul_apply, h]
    exact card_orbit_le p (by omega) h2
  · intro h
    by_cases hfix : p x = x
    · simp [hfix]
    · have hfin := orbitMap_finite hp x
      have hge : 2 ≤ (orbitMap p x).ncard := by
        have hsub : ({x, p x} : Set α) ⊆ orbitMap p x :=
          Set.pair_subset (mem_orbitMap_self p x) (apply_mem_orbitMap p x)
        have h2 := Set.ncard_le_ncard hsub hfin
        rwa [Set.ncard_pair (Ne.symm hfix)] at h2
      have hcard : (orbitMap p x).ncard = 2 := by omega
      have hcycle := hp.pow_ncard_orbitMap_apply_self x
      rw [hcard, pow_two, Equiv.Perm.mul_apply] at hcycle
      exact hcycle

/-- `hypermap.hl`:4869 `lemma_orbit_of_size_2`。 -/
theorem PermutesOn.ncard_orbit_eq_two_iff {α : Type*} {p : Equiv.Perm α} {s : Finset α}
    {x : α} (hp : PermutesOn p s) :
    (orbitMap p x).ncard = 2 ↔ p x ≠ x ∧ p (p x) = x := by
  constructor
  · intro h
    have hle : (orbitMap p x).ncard ≤ 2 := by omega
    have hpp : p (p x) = x := (PermutesOn.apply_apply_self_iff_ncard_le_two hp).mpr hle
    refine ⟨?_, hpp⟩
    intro hfix
    have h1 : orbitMap p x = {x} := (orbitMap_singleton_iff p x).mpr hfix
    rw [h1, Set.ncard_singleton] at h
    omega
  · rintro ⟨hfix, hpp⟩
    have hle : (orbitMap p x).ncard ≤ 2 := (PermutesOn.apply_apply_self_iff_ncard_le_two hp).mp hpp
    have hge : 2 ≤ (orbitMap p x).ncard := by
      have hsub : ({x, p x} : Set α) ⊆ orbitMap p x :=
        Set.pair_subset (mem_orbitMap_self p x) (apply_mem_orbitMap p x)
      have h2 := Set.ncard_le_ncard hsub (orbitMap_finite hp x)
      rwa [Set.ncard_pair (Ne.symm hfix)] at h2
    omega

/-- `hypermap.hl`:4905 `power_permutation_outside_domain`。 -/
theorem PermutesOn.pow_apply_eq_self_of_not_mem {α : Type*} {p : Equiv.Perm α} {s : Finset α}
    {x : α} (hp : PermutesOn p s) (hx : x ∉ s) (n : ℕ) : (p ^ n) x = x :=
  hp.pow n x hx

/-- `hypermap.hl`:4895 `NODE_OF_SIZE_2`。 -/
theorem node_ncard_eq_two_iff (H : Hypermap α) (x : α) :
    (H.node x).ncard = 2 ↔ H.nodeMap x ≠ x ∧ H.nodeMap (H.nodeMap x) = x :=
  PermutesOn.ncard_orbit_eq_two_iff H.nodeMap_permutes

/-- `hypermap.hl`:4915 `lemma_node_exception`。 -/
theorem node_eq_singleton_of_not_mem (H : Hypermap α) (hx : x ∉ H.darts) :
    H.node x = {x} := (orbitMap_singleton_iff H.nodeMap x).mpr (H.nodeMap_permutes x hx)

/-- `hypermap.hl`:4921 `lemma_face_exception`。 -/
theorem face_eq_singleton_of_not_mem (H : Hypermap α) (hx : x ∉ H.darts) :
    H.face x = {x} := (orbitMap_singleton_iff H.faceMap x).mpr (H.faceMap_permutes x hx)

/-- `hypermap.hl`:4927 `lemma_simple_hypermap`。 -/
theorem Simple.apply (H : Hypermap α) (hs : H.Simple) (x : α) :
    H.node x ∩ H.face x = {x} := by
  by_cases hx : x ∈ H.darts
  · exact hs x hx
  · rw [H.node_eq_singleton_of_not_mem hx, H.face_eq_singleton_of_not_mem hx,
      Set.inter_self]

/-! ## Moebius contour（`hypermap.hl`:4939–5058） -/

/-- `hypermap.hl`:4941 `is_Moebius_contour`。 -/
def IsMoebiusContour (H : Hypermap α) (p : ℕ → α) (k : ℕ) : Prop :=
  H.isInjContour p k ∧
    ∃ i j : ℕ, 0 < i ∧ i ≤ j ∧ j < k ∧ p j = H.nodeMap (p 0) ∧ p k = H.nodeMap (p i)

/-- `hypermap.hl`:4943 `lemma_contour_in_dart`。 -/
theorem contour_mem_darts (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (hp0 : p 0 ∈ H.darts) (hp : H.isContour p n) : p n ∈ H.darts := by
  induction n with
  | zero => exact hp0
  | succ k ih =>
    rw [H.isContour_succ] at hp
    rcases hp.2 with h | h
    · rw [h]; exact H.faceMap_apply_mem (ih hp.1)
    · rw [h]; exact H.nodeMap_symm_apply_mem (ih hp.1)

/-- `hypermap.hl`:4964 `lemma_darts_in_contour`。 -/
theorem contour_support_subset_darts (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (hp0 : p 0 ∈ H.darts) (hp : H.isContour p n) :
    (fun i => p i) '' ↑(Finset.range (n + 1)) ⊆ ↑H.darts := by
  rintro y ⟨i, hi, rfl⟩
  have hi' : i < n + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hi)
  exact H.contour_mem_darts hp0 (H.isContour_mono hp (by omega))

/-- `hypermap.hl`:4975 `lemma_first_dart_on_inj_contour`。 -/
theorem first_dart_mem_of_injContour (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (hn : 0 < n) (hp : H.isInjContour p n) : p 0 ∈ H.darts := by
  by_contra h0
  have key : ∀ m ≤ n, p m = p 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ k ih =>
      intro hkn
      have hk : p k = p 0 := ih (by omega)
      have hstep : H.oneStepContour (p k) (p (k + 1)) := by
        have hcont : H.isContour p n := (H.isInjContour_iff p n).mp hp |>.1
        exact (H.isContour_iff p n).mp hcont k (by omega)
      rcases hstep with h | h
      · rw [h, hk, H.faceMap_permutes _ h0]
      · rw [h, hk, H.nodeMap_permutes.symm _ h0]
  have hinj := (H.isInjContour_iff p n).mp hp |>.2
  exact hinj n 0 (by omega) (by omega) (key n le_rfl).symm

/-- `isInjContour` 的两两不同形式（`injOrbit_iff_pairwise` 的 contour 版）。 -/
theorem isInjContour_pairwise (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (hp : H.isInjContour p n) : ∀ i j : ℕ, i ≤ n → j ≤ n → p i = p j → i = j := by
  have hinj := (H.isInjContour_iff p n).mp hp |>.2
  intro i j hi hj heq
  rcases lt_trichotomy i j with hlt | heq' | hgt
  · exact absurd heq (hinj j i hj hlt)
  · exact heq'
  · exact absurd heq.symm (hinj i j hi hgt)

/-- `hypermap.hl`:5006 `lemma_darts_on_Moebius_contour`。 -/
theorem darts_on_Moebius_contour (H : Hypermap α) {p : ℕ → α} {k : ℕ}
    (hp : H.IsMoebiusContour p k) :
    2 ≤ k ∧ p 0 ∈ H.darts ∧ k + 1 ≤ H.darts.card := by
  obtain ⟨hinj, i, j, hi0, hij, hjk, -, -⟩ := hp
  refine ⟨by omega, ?_, ?_⟩
  · exact H.first_dart_mem_of_injContour (by omega) hinj
  · have hp0 : p 0 ∈ H.darts := H.first_dart_mem_of_injContour (by omega) hinj
    have hsub := H.contour_support_subset_darts hp0 (H.isContour_of_isInjContour hinj)
    have hinjOn : Set.InjOn p ↑(Finset.range (k + 1)) := by
      intro a ha b hb hab
      have ha' : a < k + 1 := Finset.mem_range.mp (Finset.mem_coe.mp ha)
      have hb' : b < k + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hb)
      exact H.isInjContour_pairwise hinj a b (by omega) (by omega) hab
    have hcard : ((fun i => p i) '' ↑(Finset.range (k + 1))).ncard = k + 1 := by
      rw [hinjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]
    have hle := Set.ncard_le_ncard hsub H.darts.finite_toSet
    rw [hcard, Set.ncard_coe_finset] at hle
    exact hle

/-- `hypermap.hl`:5029 `lemma_Moebius_contour_points_subset_darts`。 -/
theorem Moebius_contour_points_subset_darts (H : Hypermap α) {p : ℕ → α} {k : ℕ}
    (hp : H.IsMoebiusContour p k) :
    (fun i => p i) '' ↑(Finset.range (k + 1)) ⊆ ↑H.darts ∧
      ((fun i => p i) '' ↑(Finset.range (k + 1))).ncard = k + 1 := by
  obtain ⟨h2, hp0, -⟩ := H.darts_on_Moebius_contour hp
  refine ⟨H.contour_support_subset_darts hp0 (H.isContour_of_isInjContour hp.1), ?_⟩
  obtain ⟨hinj, -⟩ := hp
  have hinjOn : Set.InjOn p ↑(Finset.range (k + 1)) := by
    intro a ha b hb hab
    have ha' : a < k + 1 := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < k + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    exact H.isInjContour_pairwise hinj a b (by omega) (by omega) hab
  rw [hinjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]

/-- `hypermap.hl`:5045 `lemma_darts_is_Moebius_contour`。 -/
theorem darts_eq_of_Moebius_contour (H : Hypermap α) {p : ℕ → α} {k : ℕ}
    (hp : H.IsMoebiusContour p k) (hcard : k + 1 = H.darts.card) :
    ↑H.darts = (fun i => p i) '' ↑(Finset.range (k + 1)) := by
  obtain ⟨hsub, hncard⟩ := H.Moebius_contour_points_subset_darts hp
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hncard, hcard, Set.ncard_coe_finset])
    H.darts.finite_toSet).symm

/-- `hypermap.hl`:5053 `lemma_point_in_support_of_sequence`。 -/
theorem mem_support_iff {α : Type*} {p : ℕ → α} {k : ℕ} {x : α} :
    x ∈ (fun i => p i) '' ↑(Finset.range (k + 1)) ↔ ∃ j ≤ k, x = p j := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_range.mp hj |> Nat.lt_succ_iff.mp, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

/-- `hypermap.hl`:5055 `lemma_point_not_in_support_of_sequence`。 -/
theorem not_mem_support_iff {α : Type*} {p : ℕ → α} {k : ℕ} {x : α} :
    x ∉ (fun i => p i) '' ↑(Finset.range (k + 1)) ↔ ∀ j ≤ k, x ≠ p j := by
  rw [mem_support_iff]
  constructor
  · intro h j hj hcon
    exact h ⟨j, hj, hcon⟩
  · intro h hmem
    obtain ⟨j, hj, hcon⟩ := hmem
    exact h j hj hcon

/-- `hypermap.hl`:5174 `shift_path`。 -/
def shiftPath {α : Type*} (p : ℕ → α) (l : ℕ) : ℕ → α := fun i => p (l + i)

/-- `hypermap.hl`:5178 `lemma_shift_contour`。 -/
theorem isContour_shiftPath (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (hp : H.isContour p n) (l : ℕ) (hl : l ≤ n) : H.isContour (shiftPath p l) (n - l) := by
  rw [H.isContour_iff] at hp ⊢
  intro i hi
  have h := hp (l + i) (by omega)
  have h' : H.oneStepContour (p (l + i)) (p (l + (i + 1))) := by
    rw [(by omega : l + (i + 1) = l + i + 1)]
    exact h
  exact h'

/-- `hypermap.hl`:5191 `lemma_shift_inj_contour`。 -/
theorem isInjContour_shiftPath (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (hp : H.isInjContour p n) (l : ℕ) (hl : l ≤ n) :
    H.isInjContour (shiftPath p l) (n - l) := by
  rw [H.isInjContour_iff] at hp ⊢
  refine ⟨H.isContour_shiftPath hp.1 l hl, fun i j hi hj => ?_⟩
  exact hp.2 (l + i) (l + j) (by omega) (by omega)

/-- `hypermap.hl`:690 `join`（两路径的无缝拼接，中间不共享端点）。 -/
def joinPaths {α : Type*} (p q : ℕ → α) (n : ℕ) : ℕ → α :=
  fun i => if i ≤ n then p i else q (i - n - 1)

/-- `hypermap.hl`:693 `first_join_evaluation`。 -/
theorem joinPaths_apply_le {α : Type*} {p q : ℕ → α} {n i : ℕ} (h : i ≤ n) :
    joinPaths p q n i = p i := if_pos h

/-- `hypermap.hl`:697 `second_join_evaluation`。 -/
theorem joinPaths_apply_add {α : Type*} {p q : ℕ → α} {n : ℕ} (i : ℕ) :
    joinPaths p q n (n + (i + 1)) = q i := by
  have hle : ¬n + (i + 1) ≤ n := by omega
  have hsub : n + (i + 1) - n - 1 = i := by omega
  simp [joinPaths, hle]

/-- `hypermap.hl`:5204 `lemma_join_contours`。 -/
theorem isContour_joinPaths (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isContour p n) (hq : H.isContour q m) (h : H.oneStepContour (p n) (q 0)) :
    H.isContour (joinPaths p q n) (n + m + 1) := by
  rw [H.isContour_iff] at hp hq ⊢
  intro i hi
  by_cases hin : i < n
  · rw [joinPaths_apply_le hin.le, joinPaths_apply_le (by omega)]
    exact hp i hin
  · rcases (by omega : i = n ∨ n + 1 ≤ i) with hie | hin'
    · rw [hie, joinPaths_apply_le le_rfl]
      have h1 : joinPaths p q n (n + 1) = q 0 := by
        show joinPaths p q n (n + (0 + 1)) = q 0
        exact joinPaths_apply_add 0
      rw [h1]
      exact h
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = n + (j + 1) := ⟨i - (n + 1), by omega⟩
      have hj : j < m := by omega
      rw [joinPaths_apply_add j, show n + (j + 1) + 1 = n + ((j + 1) + 1) from by omega,
        joinPaths_apply_add (j + 1)]
      exact hq j hj

/-- `hypermap.hl`:5237 `lemma_join_inj_contours`。 -/
theorem isInjContour_joinPaths (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isInjContour p n) (hq : H.isInjContour q m)
    (h : H.oneStepContour (p n) (q 0))
    (hdisj : ∀ i ≤ n, ∀ j ≤ m, p i ≠ q j) :
    H.isInjContour (joinPaths p q n) (n + m + 1) := by
  rw [H.isInjContour_iff] at hp hq ⊢
  refine ⟨H.isContour_joinPaths hp.1 hq.1 h, fun i j hi hj => ?_⟩
  have hpj := hp.2
  have hqj := hq.2
  by_cases hi1 : i ≤ n
  · rw [joinPaths_apply_le hi1, joinPaths_apply_le (by omega)]
    exact hpj i j hi1 hj
  · obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = n + (i' + 1) := ⟨i - (n + 1), by omega⟩
    have hi'm : i' ≤ m := by omega
    rw [joinPaths_apply_add i']
    by_cases hj1 : j ≤ n
    · rw [joinPaths_apply_le hj1]
      exact hdisj j hj1 i' hi'm
    · obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = n + (j' + 1) := ⟨j - (n + 1), by omega⟩
      have hj' : j' < i' := by omega
      rw [joinPaths_apply_add j']
      exact hqj i' j' hi'm (by omega)

/-- `is_glueing`（`hypermap.hl`:653）：`glue` 的无重叠拼接条件。 -/
def IsGlueing {α : Type*} (p q : ℕ → α) (n m : ℕ) : Prop :=
  p n = q 0 ∧ ∀ j : ℕ, 1 ≤ j → j ≤ m → q j ∉ (fun i => p i) '' ↑(Finset.range (n + 1))

/-- `hypermap.hl`:5249 `lemma_glue_inj_contours`。 -/
theorem isInjContour_gluePaths (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isInjContour p n) (hq : H.isInjContour q m) (hg : IsGlueing p q n m) :
    H.isInjContour (gluePaths p q n) (n + m) := by
  obtain ⟨hg0, hgdisj⟩ := hg
  rw [H.isInjContour_iff] at hp hq ⊢
  refine ⟨H.isContour_gluePaths hp.1 hq.1 hg0, fun i j hi hj => ?_⟩
  have hpj := hp.2
  have hqj := hq.2
  by_cases hi1 : i ≤ n
  · rw [gluePaths_apply_le hi1, gluePaths_apply_le (by omega)]
    exact hpj i j hi1 hj
  · obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = n + i' := ⟨i - n, by omega⟩
    have hi'0 : 1 ≤ i' := by omega
    have hi'm : i' ≤ m := by omega
    rw [gluePaths_apply_add hg0 i']
    by_cases hj1 : j ≤ n
    · rw [gluePaths_apply_le hj1]
      intro hcon
      exact hgdisj i' hi'0 hi'm ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), hcon⟩
    · obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = n + j' := ⟨j - n, by omega⟩
      have hj'0 : 1 ≤ j' := by omega
      have hj'lt : j' < i' := by omega
      rw [gluePaths_apply_add hg0 j']
      exact hqj i' j' hi'm (by omega)

/-- `hypermap.hl`:5257 `concatenate_two_contours`。 -/
theorem concatenate_two_contours (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isInjContour p n) (hq : H.isInjContour q m) (h : p n = q 0)
    (hdisj : ∀ j : ℕ, 0 < j → j ≤ m → ∀ i ≤ n, q j ≠ p i) :
    ∃ g : ℕ → α, g 0 = p 0 ∧ g (n + m) = q m ∧ H.isInjContour g (n + m) ∧
      (∀ i ≤ n, g i = p i) ∧ (∀ i ≤ m, g (n + i) = q i) := by
  have hg : IsGlueing p q n m := by
    refine ⟨h, fun j hj1 hjm hmem => ?_⟩
    obtain ⟨i, hi, hiq⟩ := hmem
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_coe.mp hi))
    exact hdisj j (by omega) hjm i hi_le hiq.symm
  exact ⟨gluePaths p q n, gluePaths_apply_le (Nat.zero_le n), gluePaths_apply_add h m,
    H.isInjContour_gluePaths hp hq hg, fun i hi => gluePaths_apply_le hi,
    fun i _ => gluePaths_apply_add h i⟩

/-- `hypermap.hl`:5266 `concatenate_two_disjoint_contours`。 -/
theorem concatenate_two_disjoint_contours (H : Hypermap α) {p q : ℕ → α} {n m : ℕ}
    (hp : H.isInjContour p n) (hq : H.isInjContour q m)
    (h : H.oneStepContour (p n) (q 0))
    (hdisj : ∀ i ≤ n, ∀ j ≤ m, q j ≠ p i) :
    ∃ g : ℕ → α, g 0 = p 0 ∧ g (n + m + 1) = q m ∧ H.isInjContour g (n + m + 1) ∧
      (∀ i ≤ n, g i = p i) ∧ (∀ i ≤ m, g (n + i + 1) = q i) :=
  ⟨joinPaths p q n, joinPaths_apply_le (Nat.zero_le n),
    by rw [show n + m + 1 = n + (m + 1) from by omega, joinPaths_apply_add m],
    H.isInjContour_joinPaths hp hq h (fun i hi j hj => (hdisj i hi j hj).symm),
    fun i hi => joinPaths_apply_le hi, fun i _ => joinPaths_apply_add i⟩

/-- `hypermap.hl`:5353 `lemma_one_step_contour`。 -/
theorem oneStepContour_iff (H : Hypermap α) (x y : α) :
    H.oneStepContour x y ↔ y = H.faceMap x ∨ x = H.nodeMap y := by
  unfold oneStepContour
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((Equiv.symm_apply_eq H.nodeMap).mp h.symm)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (((Equiv.symm_apply_eq H.nodeMap).mpr h).symm)

/-- `hypermap.hl`:5360 `lemma_only_one_orbit`。 -/
theorem PermutesOn.setOfOrbits_eq_singleton {α : Type*} {p : Equiv.Perm α} {s : Finset α}
    {x : α} (hp : PermutesOn p s) (h : orbitMap p x = ↑s) :
    setOfOrbits s p = {orbitMap p x} := by
  have hx : x ∈ s := by
    have h1 : x ∈ orbitMap p x := mem_orbitMap_self p x
    rw [h] at h1
    exact Finset.mem_coe.mp h1
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff]
    have hne : (orbitMap p y ∩ orbitMap p x).Nonempty := by
      refine ⟨y, mem_orbitMap_self p y, ?_⟩
      have hsub := orbitMap_subset_of_permutesOn hp hy
      rw [← h] at hsub
      exact hsub (mem_orbitMap_self p y)
    rcases orbitMap_disjoint_or_eq hp y x with hdis | heq
    · exact absurd hne (hdis.symm ▸ Set.not_nonempty_empty)
    · exact heq
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu, h]
    exact ⟨x, hx, h⟩

/-- `hypermap.hl`:5383 `lemma_only_one_component`。 -/
theorem setOfComponents_eq_singleton (H : Hypermap α) {x : α}
    (h : H.combComponent x = ↑H.darts) : H.setOfComponents = {H.combComponent x} := by
  have hx : x ∈ H.darts := by
    have h1 : x ∈ H.combComponent x := H.mem_combComponent_self x
    rw [h] at h1
    exact Finset.mem_coe.mp h1
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff]
    have hne : (H.combComponent y ∩ H.combComponent x).Nonempty :=
      ⟨y, H.mem_combComponent_self y, by rw [h]; exact Finset.mem_coe.mp hy⟩
    rcases H.partition_components y x with heq | hdis
    · exact heq
    · exact absurd hne (hdis.symm ▸ Set.not_nonempty_empty)
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact ⟨x, hx, rfl⟩

/-- `hypermap.hl`:5061 `lemma_eliminate_dart_ouside_Moebius_contour`。
`x` 避开整个 contour 时，walkup 保持 Moebius contour（`nodeMap_walkup`/
`faceMap_walkup` 的第三分量在接缝外逐点成立）。 -/
theorem isMoebiusContour_edgeWalkup_of_not_mem_support (H : Hypermap α) {p : ℕ → α} {k : ℕ}
    (hp : H.IsMoebiusContour p k) {x : α}
    (hx : x ∉ (fun i => p i) '' ↑(Finset.range (k + 1))) :
    (H.edgeWalkup x).IsMoebiusContour p k := by
  have hni : ∀ i ≤ k, p i ≠ x := by
    intro i hi hcon
    exact hx ⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), hcon⟩
  obtain ⟨hinj, i, j, hi0, hij, hjk, h1, h2⟩ := hp
  have keyN : ∀ a ≤ k, ∀ b ≤ k, H.nodeMap (p a) = p b →
      (H.edgeWalkup x).nodeMap (p a) = p b := by
    intro a ha b hb hab
    have h3 : p a ≠ H.nodeMap.symm x := by
      intro hcon
      apply hx
      refine ⟨b, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), ?_⟩
      show p b = x
      rw [← hab, hcon]
      exact Equiv.apply_symm_apply _ _
    exact ((H.nodeMap_walkup x (p a)).2.2 ⟨hni a ha, h3⟩).trans hab
  have keyNs : ∀ a ≤ k, ∀ b ≤ k, H.nodeMap.symm (p a) = p b →
      (H.edgeWalkup x).nodeMap.symm (p a) = p b := by
    intro a ha b hb hab
    have h4 : (H.edgeWalkup x).nodeMap (p b) = p a :=
      keyN b hb a ha ((Equiv.symm_apply_eq H.nodeMap).mp hab).symm
    exact (Equiv.symm_apply_eq (H.edgeWalkup x).nodeMap).mpr h4.symm
  have keyF : ∀ a ≤ k, ∀ b ≤ k, H.faceMap (p a) = p b →
      (H.edgeWalkup x).faceMap (p a) = p b := by
    intro a ha b hb hab
    have h3 : p a ≠ H.faceMap.symm x := by
      intro hcon
      apply hx
      refine ⟨b, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), ?_⟩
      show p b = x
      rw [← hab, hcon]
      exact Equiv.apply_symm_apply _ _
    exact ((H.faceMap_walkup x (p a)).2.2 ⟨hni a ha, h3⟩).trans hab
  have hcont : (H.edgeWalkup x).isInjContour p k := by
    rw [H.isInjContour_iff p k] at hinj
    rw [(H.edgeWalkup x).isInjContour_iff p k]
    refine ⟨?_, hinj.2⟩
    rw [(H.edgeWalkup x).isContour_iff]
    intro a ha
    have hstep := (H.isContour_iff p k).mp hinj.1 a ha
    rcases hstep with hstep | hstep
    · exact Or.inl (keyF a (by omega) (a + 1) (by omega) hstep.symm).symm
    · exact Or.inr (keyNs a (by omega) (a + 1) (by omega) hstep.symm).symm
  refine ⟨hcont, i, j, hi0, hij, hjk, ?_, ?_⟩
  · exact (keyN 0 (by omega) j (by omega) h1.symm).symm
  · exact (keyN i (by omega) k (by omega) h2.symm).symm

/-- `hypermap.hl`:5279 `lemmaQZTPGJV`：contour 可提取为同端点的 inj contour。 -/
theorem exists_injContour_of_isContour (H : Hypermap α) {p : ℕ → α} {n : ℕ}
    (hp : H.isContour p n) :
    ∃ q : ℕ → α, ∃ m : ℕ, m ≤ n ∧ q 0 = p 0 ∧ q m = p n ∧ H.isInjContour q m ∧
      (∀ i < m, ∃ j : ℕ, i ≤ j ∧ j < n ∧ q i = p j ∧ q (i + 1) = p (j + 1)) := by
  induction n with
  | zero => exact ⟨p, 0, Nat.le_refl 0, rfl, rfl, trivial, fun i hi => by omega⟩
  | succ n ihn =>
    rw [H.isContour_succ] at hp
    obtain ⟨q, m, hmn, hq0, hqm, hq, hseg⟩ := ihn hp.1
    by_cases hk : ∃ k ≤ m, q k = p (n + 1)
    · obtain ⟨k, hkm, hkeq⟩ := hk
      refine ⟨q, k, by omega, hq0, hkeq, H.isInjContour_mono hq hkm, fun i hi => ?_⟩
      obtain ⟨j, hij, hjn, h1, h2⟩ := hseg i (by omega)
      exact ⟨j, hij, by omega, h1, h2⟩
    · -- 在末尾接一段常值路径 `p (n+1)`（长度 1）
      have hdisj : ∀ i ≤ m, ∀ j ≤ 0, (fun _ => p (n + 1)) j ≠ q i := by
        intro i hi j hj
        simp only
        intro hcon
        apply hk
        exact ⟨i, hi, hcon.symm⟩
      obtain ⟨g, hg0, hgm, hgpath, hg1, hg2⟩ := H.concatenate_two_disjoint_contours hq
        (by trivial : H.isInjContour (fun _ => p (n + 1)) 0) (by simpa [hqm] using hp.2) hdisj
      refine ⟨g, m + 1, by omega, hg0.trans hq0, hgm, hgpath, ?_⟩
      intro i hi
      rcases (by omega : i < m ∨ i = m) with him | hie
      · obtain ⟨j, hij, hjn, h1, h2⟩ := hseg i him
        refine ⟨j, hij, by omega, ?_, ?_⟩
        · rw [hg1 i (by omega)]; exact h1
        · rw [hg1 (i + 1) (by omega)]; exact h2
      · refine ⟨n, by omega, by omega, ?_, ?_⟩
        · rw [hie, hg1 m (Nat.le_refl m)]
          exact hqm
        · rw [hie, show m + 1 = m + 0 + 1 from by omega, hg2 0 (by omega)]

/-- `hypermap.hl`:5629 `dart_face_walkup`。 -/
theorem darts_faceWalkup (H : Hypermap α) (x : α) :
    (H.faceWalkup x).darts = H.darts.erase x := rfl

/-- `hypermap.hl`:5636 `lemma_card_face_walkup_dart`。 -/
theorem card_faceWalkup_dart (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.darts.card = (H.faceWalkup x).darts.card + 1 := by
  show H.darts.card = (H.darts.erase x).card + 1
  rw [Finset.card_erase_of_mem hx]
  have hpos : 0 < H.darts.card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- `hypermap.hl`:5662 `dart_node_walkup`。 -/
theorem darts_nodeWalkup (H : Hypermap α) (x : α) :
    (H.nodeWalkup x).darts = H.darts.erase x := rfl

/-- `hypermap.hl`:5669 `lemma_card_node_walkup_dart`。 -/
theorem card_nodeWalkup_dart (H : Hypermap α) {x : α} (hx : x ∈ H.darts) :
    H.darts.card = (H.nodeWalkup x).darts.card + 1 := by
  show H.darts.card = (H.darts.erase x).card + 1
  rw [Finset.card_erase_of_mem hx]
  have hpos : 0 < H.darts.card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- `hypermap.hl`:5641 `face_map_face_walkup`（即 `edgeMap_walkup` 在 `shift²` 上的实例）。 -/
theorem faceMap_faceWalkup (H : Hypermap α) (x y : α) :
    (H.faceWalkup x).faceMap x = x ∧
    (H.edgeMap x ≠ x ∧ H.faceMap x ≠ x →
      (H.faceWalkup x).faceMap (H.edgeMap x) = H.faceMap x) ∧
    (H.nodeMap⁻¹ x ≠ x ∧ H.faceMap⁻¹ x ≠ x →
      (H.faceWalkup x).faceMap (H.faceMap⁻¹ x) = H.nodeMap⁻¹ x) ∧
    (y ≠ x ∧ y ≠ H.faceMap⁻¹ x ∧ y ≠ H.edgeMap x →
      (H.faceWalkup x).faceMap y = H.faceMap y) :=
  (H.shift.shift).edgeMap_walkup x y

/-- `hypermap.hl`:5652 `node_map_face_walkup`（即 `faceMap_walkup` 在 `shift²` 上的实例）。 -/
theorem nodeMap_faceWalkup (H : Hypermap α) (x y : α) :
    (H.faceWalkup x).nodeMap x = x ∧
    (H.faceWalkup x).nodeMap (H.nodeMap.symm x) = H.nodeMap x ∧
    (y ≠ x ∧ y ≠ H.nodeMap.symm x → (H.faceWalkup x).nodeMap y = H.nodeMap y) :=
  (H.shift.shift).faceMap_walkup x y

/-- `hypermap.hl`:5675 `node_map_node_walkup`（即 `edgeMap_walkup` 在 `shift` 上的实例）。 -/
theorem nodeMap_nodeWalkup (H : Hypermap α) (x y : α) :
    (H.nodeWalkup x).nodeMap x = x ∧
    (H.faceMap x ≠ x ∧ H.nodeMap x ≠ x →
      (H.nodeWalkup x).nodeMap (H.faceMap x) = H.nodeMap x) ∧
    (H.edgeMap⁻¹ x ≠ x ∧ H.nodeMap⁻¹ x ≠ x →
      (H.nodeWalkup x).nodeMap (H.nodeMap⁻¹ x) = H.edgeMap⁻¹ x) ∧
    (y ≠ x ∧ y ≠ H.nodeMap⁻¹ x ∧ y ≠ H.faceMap x →
      (H.nodeWalkup x).nodeMap y = H.nodeMap y) :=
  (H.shift).edgeMap_walkup x y

/-- `hypermap.hl`:5683 `face_map_node_walkup`（即 `nodeMap_walkup` 在 `shift` 上的实例）。 -/
theorem faceMap_nodeWalkup (H : Hypermap α) (x y : α) :
    (H.nodeWalkup x).faceMap x = x ∧
    (H.nodeWalkup x).faceMap (H.faceMap.symm x) = H.faceMap x ∧
    (y ≠ x ∧ y ≠ H.faceMap.symm x → (H.nodeWalkup x).faceMap y = H.faceMap y) :=
  (H.shift).nodeMap_walkup x y

/-- inj 序列中不同下标对应不同点的常用形式。 -/
theorem ne_of_pairwise {α : Type*} [DecidableEq α] {p : ℕ → α} {k : ℕ}
    (hinj : ∀ i j : ℕ, i ≤ k → j ≤ k → p i = p j → i = j) {a b : ℕ}
    (ha : a ≤ k) (hb : b ≤ k) (hab : a ≠ b) : p a ≠ p b :=
  fun hcon => hab (hinj a b ha hb hcon)

/-- `hypermap.hl`:5691 `lemma_face_walkup_second_segment_contour`。 -/
theorem isInjContour_faceWalkup_shift (H : Hypermap α) {p : ℕ → α} {k m : ℕ}
    (hp : H.isInjContour p k) (hm : m < k) (hstep : H.nodeMap (p (m + 1)) = p m) :
    (H.faceWalkup (p m)).isInjContour (shiftPath p (m + 1)) (k - (m + 1)) := by
  have hinj := H.isInjContour_pairwise hp
  have hcont := H.isContour_of_isInjContour hp
  rw [(H.faceWalkup (p m)).isInjContour_iff]
  refine ⟨?_, fun i j hi hj hcon =>
    absurd (hinj (m + 1 + j) (m + 1 + i) (by omega) (by omega) hcon) (by omega)⟩
  rw [(H.faceWalkup (p m)).isContour_iff]
  intro i hi
  have hst := (H.isContour_iff p k).mp hcont (m + 1 + i) (by omega)
  show (H.faceWalkup (p m)).oneStepContour (p (m + 1 + i)) (p ((m + 1 + i) + 1))
  rcases hst with hst | hst
  · -- f 步：用 `faceMap_faceWalkup` 第 4 分量
    have hne1 := ne_of_pairwise hinj (by omega) (by omega) (by omega : m + 1 + i ≠ m)
    have hne2 : p (m + 1 + i) ≠ H.faceMap.symm (p m) := by
      intro hcon
      have h1 : p ((m + 1 + i) + 1) = p m := by
        rw [hst, hcon]; exact Equiv.apply_symm_apply _ _
      exact absurd (hinj ((m + 1 + i) + 1) m (by omega) (by omega) h1) (by omega)
    have hne3 : p (m + 1 + i) ≠ H.edgeMap (p m) := by
      intro hcon
      have h1 : H.nodeMap (p ((m + 1 + i) + 1)) = p m := by
        have h2 : H.faceMap (H.edgeMap (p m)) = p ((m + 1 + i) + 1) := (hcon ▸ hst).symm
        rw [← h2]; exact H.nfe_apply (p m)
      have h3 := H.nodeMap.injective (h1.trans hstep.symm)
      exact absurd (hinj ((m + 1 + i) + 1) (m + 1) (by omega) (by omega) h3) (by omega)
    exact Or.inl (hst.trans ((H.faceMap_faceWalkup (p m) _).2.2.2 ⟨hne1, hne2, hne3⟩).symm)
  · -- n⁻¹ 步：用 `nodeMap_faceWalkup` 第 3 分量
    have hne1 := ne_of_pairwise hinj (by omega) (by omega)
      (by omega : (m + 1 + i) + 1 ≠ m)
    have hne2 : p ((m + 1 + i) + 1) ≠ H.nodeMap.symm (p m) := by
      intro hcon
      have h1 : H.nodeMap (p ((m + 1 + i) + 1)) = p m := by
        rw [hcon]; exact Equiv.apply_symm_apply _ _
      have h2 := H.nodeMap.injective (h1.trans hstep.symm)
      exact absurd (hinj ((m + 1 + i) + 1) (m + 1) (by omega) (by omega) h2) (by omega)
    have h4 : H.nodeMap (p ((m + 1 + i) + 1)) = p (m + 1 + i) :=
      ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
    have h5 : (H.faceWalkup (p m)).nodeMap (p ((m + 1 + i) + 1)) = p (m + 1 + i) :=
      ((H.nodeMap_faceWalkup (p m) _).2.2 ⟨hne1, hne2⟩).trans h4
    exact Or.inr ((Equiv.symm_apply_eq (H.faceWalkup (p m)).nodeMap).mpr h5.symm).symm

/-- `hypermap.hl`:5774 `lemma_face_walkup_eliminate_dart_on_Moebius_contour`。 -/
theorem isInjContour_faceWalkup_eliminate (H : Hypermap α) {p : ℕ → α} {k m : ℕ}
    (hp : H.isInjContour p k) (hm0 : 0 < m) (hm : m < k)
    (hstep : H.nodeMap (p (m + 1)) = p m) :
    (H.faceWalkup (p m)).isInjContour p (m - 1) ∧
      (H.faceWalkup (p m)).isInjContour (shiftPath p (m + 1)) (k - m - 1) ∧
      (H.faceWalkup (p m)).oneStepContour (p (m - 1)) (p (m + 1)) := by
  have hinj := H.isInjContour_pairwise hp
  have hcont := H.isContour_of_isInjContour hp
  refine ⟨?_, H.isInjContour_faceWalkup_shift hp hm hstep, ?_⟩
  · rw [(H.faceWalkup (p m)).isInjContour_iff]
    refine ⟨?_, fun i j hi hj hcon => absurd (hinj i j (by omega) (by omega) hcon.symm) (by omega)⟩
    rw [(H.faceWalkup (p m)).isContour_iff]
    intro i hi
    have hst := (H.isContour_iff p k).mp hcont i (by omega)
    rcases hst with hst | hst
    · have hne1 := ne_of_pairwise hinj (by omega) (by omega) (by omega : i ≠ m)
      have hne2 : p i ≠ H.faceMap.symm (p m) := by
        intro hcon
        have h1 : p (i + 1) = p m := by
          rw [hst, hcon]; exact Equiv.apply_symm_apply _ _
        exact absurd (hinj (i + 1) m (by omega) (by omega) h1) (by omega)
      have hne3 : p i ≠ H.edgeMap (p m) := by
        intro hcon
        have h1 : H.nodeMap (p (i + 1)) = p m := by
          have h2 : H.faceMap (H.edgeMap (p m)) = p (i + 1) := (hcon ▸ hst).symm
          rw [← h2]; exact H.nfe_apply (p m)
        have h3 := H.nodeMap.injective (h1.trans hstep.symm)
        exact absurd (hinj (i + 1) (m + 1) (by omega) (by omega) h3) (by omega)
      exact Or.inl (hst.trans ((H.faceMap_faceWalkup (p m) _).2.2.2 ⟨hne1, hne2, hne3⟩).symm)
    · have hne1 := ne_of_pairwise hinj (by omega) (by omega) (by omega : i + 1 ≠ m)
      have hne2 : p (i + 1) ≠ H.nodeMap.symm (p m) := by
        intro hcon
        have h1 : H.nodeMap (p (i + 1)) = p m := by
          rw [hcon]; exact Equiv.apply_symm_apply _ _
        have h2 := H.nodeMap.injective (h1.trans hstep.symm)
        exact absurd (hinj (i + 1) (m + 1) (by omega) (by omega) h2) (by omega)
      have h4 : H.nodeMap (p (i + 1)) = p i := ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
      have h5 : (H.faceWalkup (p m)).nodeMap (p (i + 1)) = p i :=
        ((H.nodeMap_faceWalkup (p m) _).2.2 ⟨hne1, hne2⟩).trans h4
      exact Or.inr ((Equiv.symm_apply_eq (H.faceWalkup (p m)).nodeMap).mpr h5.symm).symm
  · -- 连接步：`p (m-1) → p (m+1)`
    have hst := (H.isContour_iff p k).mp hcont (m - 1) (by omega)
    rw [(by omega : m - 1 + 1 = m)] at hst
    rcases hst with hst | hst
    · -- H 中 `p (m-1) →f p m`：用 `faceMap_faceWalkup` 第 3 分量
      have hL : p (m - 1) = H.faceMap.symm (p m) := by
        rw [hst]; exact (Equiv.symm_apply_apply _ _).symm
      have hcond1 : H.nodeMap⁻¹ (p m) ≠ p m := by
        show H.nodeMap.symm (p m) ≠ p m
        have h1 : H.nodeMap.symm (p m) = p (m + 1) :=
          (Equiv.symm_apply_eq H.nodeMap).mpr hstep.symm
        rw [h1]
        exact ne_of_pairwise hinj (by omega) (by omega) (by omega : m + 1 ≠ m)
      have hcond2 : H.faceMap⁻¹ (p m) ≠ p m := by
        show H.faceMap.symm (p m) ≠ p m
        rw [← hL]
        exact ne_of_pairwise hinj (by omega) (by omega) (by omega : m - 1 ≠ m)
      have h1 : (H.faceWalkup (p m)).faceMap (p (m - 1)) = H.nodeMap⁻¹ (p m) := by
        rw [hL]
        exact (H.faceMap_faceWalkup (p m) (p m)).2.2.1 ⟨hcond1, hcond2⟩
      have h2 : H.nodeMap.symm (p m) = p (m + 1) :=
        (Equiv.symm_apply_eq H.nodeMap).mpr hstep.symm
      exact Or.inl (h1.trans h2).symm
    · -- H 中 `n (p m) = p (m-1)`：用 `nodeMap_faceWalkup` 第 2 分量
      have hL : H.nodeMap (p m) = p (m - 1) := ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
      have h1 : (H.faceWalkup (p m)).nodeMap (p (m + 1)) = H.nodeMap (p m) := by
        have h2 : p (m + 1) = H.nodeMap.symm (p m) :=
          ((Equiv.symm_apply_eq H.nodeMap).mpr hstep.symm).symm
        rw [h2]
        exact (H.nodeMap_faceWalkup (p m) (p m)).2.1
      exact Or.inr (((Equiv.symm_apply_eq (H.faceWalkup (p m)).nodeMap).mpr
        (h1.trans hL).symm).symm)

/-- `hypermap.hl`:5888 `lemma_node_walkup_second_segment_contour`。 -/
theorem isInjContour_nodeWalkup_shift (H : Hypermap α) {p : ℕ → α} {k m : ℕ}
    (hp : H.isInjContour p k) (hm : m < k) (hstep : p (m + 1) = H.faceMap (p m)) :
    (H.nodeWalkup (p m)).isInjContour (shiftPath p (m + 1)) (k - (m + 1)) := by
  have hinj := H.isInjContour_pairwise hp
  have hcont := H.isContour_of_isInjContour hp
  rw [(H.nodeWalkup (p m)).isInjContour_iff]
  refine ⟨?_, fun i j hi hj hcon =>
    absurd (hinj (m + 1 + j) (m + 1 + i) (by omega) (by omega) hcon) (by omega)⟩
  rw [(H.nodeWalkup (p m)).isContour_iff]
  intro i hi
  have hst := (H.isContour_iff p k).mp hcont (m + 1 + i) (by omega)
  show (H.nodeWalkup (p m)).oneStepContour (p (m + 1 + i)) (p ((m + 1 + i) + 1))
  rcases hst with hst | hst
  · have hne1 := ne_of_pairwise hinj (by omega) (by omega) (by omega : m + 1 + i ≠ m)
    have hne2 : p (m + 1 + i) ≠ H.faceMap.symm (p m) := by
      intro hcon
      have h1 : p ((m + 1 + i) + 1) = p m := by
        rw [hst, hcon]; exact Equiv.apply_symm_apply _ _
      exact absurd (hinj ((m + 1 + i) + 1) m (by omega) (by omega) h1) (by omega)
    exact Or.inl (hst.trans ((H.faceMap_nodeWalkup (p m) _).2.2 ⟨hne1, hne2⟩).symm)
  · have hne1 := ne_of_pairwise hinj (by omega) (by omega)
      (by omega : (m + 1 + i) + 1 ≠ m)
    have hne2 : p ((m + 1 + i) + 1) ≠ H.nodeMap⁻¹ (p m) := by
      intro hcon
      have h1 : H.nodeMap (p ((m + 1 + i) + 1)) = p m := by
        rw [hcon]; exact Equiv.apply_symm_apply _ _
      have h2 : p (m + 1 + i) = p m := by
        have h3 := ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
        rw [h1] at h3
        exact h3.symm
      exact absurd (hinj (m + 1 + i) m (by omega) (by omega) h2) (by omega)
    have hne3 : p ((m + 1 + i) + 1) ≠ H.faceMap (p m) := by
      rw [← hstep]
      exact ne_of_pairwise hinj (by omega) (by omega)
        (by omega : (m + 1 + i) + 1 ≠ m + 1)
    have h4 : H.nodeMap (p ((m + 1 + i) + 1)) = p (m + 1 + i) :=
      ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
    have h5 : (H.nodeWalkup (p m)).nodeMap (p ((m + 1 + i) + 1)) = p (m + 1 + i) :=
      ((H.nodeMap_nodeWalkup (p m) _).2.2.2 ⟨hne1, hne2, hne3⟩).trans h4
    exact Or.inr ((Equiv.symm_apply_eq (H.nodeWalkup (p m)).nodeMap).mpr h5.symm).symm

/-- `hypermap.hl`:5969 `lemma_node_walkup_eliminate_dart_on_Moebius_contour`。 -/
theorem isInjContour_nodeWalkup_eliminate (H : Hypermap α) {p : ℕ → α} {k m : ℕ}
    (hp : H.isInjContour p k) (hm0 : 0 < m) (hm : m < k)
    (hstep : p (m + 1) = H.faceMap (p m)) :
    (H.nodeWalkup (p m)).isInjContour p (m - 1) ∧
      (H.nodeWalkup (p m)).isInjContour (shiftPath p (m + 1)) (k - m - 1) ∧
      (H.nodeWalkup (p m)).oneStepContour (p (m - 1)) (p (m + 1)) := by
  have hinj := H.isInjContour_pairwise hp
  have hcont := H.isContour_of_isInjContour hp
  refine ⟨?_, H.isInjContour_nodeWalkup_shift hp hm hstep, ?_⟩
  · rw [(H.nodeWalkup (p m)).isInjContour_iff]
    refine ⟨?_, fun i j hi hj hcon => absurd (hinj i j (by omega) (by omega) hcon.symm) (by omega)⟩
    rw [(H.nodeWalkup (p m)).isContour_iff]
    intro i hi
    have hst := (H.isContour_iff p k).mp hcont i (by omega)
    rcases hst with hst | hst
    · have hne1 := ne_of_pairwise hinj (by omega) (by omega) (by omega : i ≠ m)
      have hne2 : p i ≠ H.faceMap.symm (p m) := by
        intro hcon
        have h1 : p (i + 1) = p m := by
          rw [hst, hcon]; exact Equiv.apply_symm_apply _ _
        exact absurd (hinj (i + 1) m (by omega) (by omega) h1) (by omega)
      exact Or.inl (hst.trans ((H.faceMap_nodeWalkup (p m) _).2.2 ⟨hne1, hne2⟩).symm)
    · have hne1 := ne_of_pairwise hinj (by omega) (by omega) (by omega : i + 1 ≠ m)
      have hne2 : p (i + 1) ≠ H.nodeMap⁻¹ (p m) := by
        intro hcon
        have h1 : H.nodeMap (p (i + 1)) = p m := by
          rw [hcon]; exact Equiv.apply_symm_apply _ _
        have h2 : p i = p m := by
          have h3 := ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
          rw [h1] at h3
          exact h3.symm
        exact absurd (hinj i m (by omega) (by omega) h2) (by omega)
      have hne3 : p (i + 1) ≠ H.faceMap (p m) := by
        rw [← hstep]
        exact ne_of_pairwise hinj (by omega) (by omega) (by omega : i + 1 ≠ m + 1)
      have h4 : H.nodeMap (p (i + 1)) = p i := ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
      have h5 : (H.nodeWalkup (p m)).nodeMap (p (i + 1)) = p i :=
        ((H.nodeMap_nodeWalkup (p m) _).2.2.2 ⟨hne1, hne2, hne3⟩).trans h4
      exact Or.inr ((Equiv.symm_apply_eq (H.nodeWalkup (p m)).nodeMap).mpr h5.symm).symm
  · have hst := (H.isContour_iff p k).mp hcont (m - 1) (by omega)
    rw [(by omega : m - 1 + 1 = m)] at hst
    rcases hst with hst | hst
    · -- H 中 `p (m-1) →f p m`：`fNode (f⁻¹ (p m)) = f (p m) = p (m+1)`
      have hL : p (m - 1) = H.faceMap.symm (p m) := by
        rw [hst]; exact (Equiv.symm_apply_apply _ _).symm
      have h1 : (H.nodeWalkup (p m)).faceMap (p (m - 1)) = H.faceMap (p m) := by
        rw [hL]
        exact (H.faceMap_nodeWalkup (p m) (p m)).2.1
      exact Or.inl (h1.trans hstep.symm).symm
    · -- H 中 `n (p m) = p (m-1)`：`nodeNode (f (p m)) = n (p m)`
      have hL : H.nodeMap (p m) = p (m - 1) := ((Equiv.symm_apply_eq H.nodeMap).mp hst.symm).symm
      have hcond1 : H.faceMap (p m) ≠ p m := by
        rw [← hstep]
        exact ne_of_pairwise hinj (by omega) (by omega) (by omega : m + 1 ≠ m)
      have hcond2 : H.nodeMap (p m) ≠ p m := by
        rw [hL]
        exact ne_of_pairwise hinj (by omega) (by omega) (by omega : m - 1 ≠ m)
      have h1 : (H.nodeWalkup (p m)).nodeMap (p (m + 1)) = H.nodeMap (p m) := by
        rw [hstep]
        exact (H.nodeMap_nodeWalkup (p m) (p m)).2.1 ⟨hcond1, hcond2⟩
      exact Or.inr (((Equiv.symm_apply_eq (H.nodeWalkup (p m)).nodeMap).mpr
        (h1.trans hL).symm).symm)

end Hypermap

end Kepler.Text
