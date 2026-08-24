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

end Kepler.Text
