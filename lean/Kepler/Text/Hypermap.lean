/-
Port of the HOL Light Flyspeck hypermap theory (core definition layer).

Source: `reference/flyspeck/text_formalization/hypermap/hypermap.hl`
(Flyspeck book formalization, Tran Nam Trung, 2010).

Coverage:
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

end Kepler.Text
