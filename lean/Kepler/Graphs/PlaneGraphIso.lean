/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `PlaneGraphIso.thy`.

Source: `reference/afp-flyspeck-tame/PlaneGraphIso.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

## Translation conventions

- `'a fgraph = 'a list list` ↦ `fgraph α := List (List α)`;
  `'a Fgraph = 'a list set` ↦ `Fgraph α := Set (List α)`.
  `set Fs` (the set of faces of an fgraph) ↦ `{F | F ∈ Fs}`.
- Face congruence `F₁ ≅ F₂ ≡ ∃n. F₂ = rotate n F₁` is NOT redefined here:
  it is `Kepler.Graphs.cong` from `RotationLemmas.lean`, together with its
  refl/sym/trans/length/mem/distinct/map lemmas.
- Isabelle works with quotients `Fs // {≅}` (sets of congruence classes).
  Lean has no directly matching quotient-set API, so `A //{≅} = B //{≅}` is
  translated by the equivalent class-free characterization
    `(∀ F ∈ A, ∃ F' ∈ B, cong F F') ∧ (∀ F' ∈ B, ∃ F ∈ A, cong F F')`
  (two sets have the same congruence classes iff every member of each side is
  congruent to some member of the other side; classes are nonempty and
  `[x] = [y] ↔ x ≅ y`).  This is exactly the form Isabelle's proofs use via
  `quotientE` (see e.g. the proof of `is_pr_Hom_trans`).
  Accordingly `is_pr_Hom φ Fs₁ Fs₂` translates
  `(map φ ` Fs₁)//{≅} = Fs₂//{≅}` in that unfolded form.
- `inj_on (λxs. {xs}//{≅}) (set Fs)` (injectivity of the congruence-class map)
  ↦ `noncong Fs : ∀ F₁ ∈ Fs, ∀ F₂ ∈ Fs, cong F₁ F₂ → F₁ = F₂`
  (equivalent by `[x] = [y] ↔ x ≅ y`).
- Partial maps `'a ⇀ 'b` ↦ `α → Option β`; `map_of` ↦ `mapOf`,
  `m ++ m'` (right-biased) ↦ `mapAdd m m'`, `dom m` ↦ `mapDom m`,
  `f ⊆ₘ g` ↦ `mapLe f g`, `Map.empty` ↦ `fun _ => none`,
  `the ∘ m` ↦ `fun x => (m x).getD default` (needs `Inhabited β`,
  as does Isabelle's `the` on `None`, which is `undefined`).
- `remove1` ↦ `List.erase` (hence `BEq`/`LawfulBEq` constraints where the
  Isabelle original uses plain equality).
## Scope

Ported: the face-congruence extras (`list_cong_rev_iff`, `congs_map_eq_iff`),
`is_pr_Hom`/`is_pr_Iso`/`is_pr_iso` + `is_pr_Hom_trans`/`is_pr_Hom_rev`/
`pr_Hom_pres_nodes`/`is_Hom_distinct`/`pr_iso_same_no_nodes`, `is_iso_Cons`
(which subsumes the `is_pr_Iso_rec` detour), the executable chain
`oneone`/`compat`/`merge0`/`merge`/`pr_iso_test_rec`/`pr_iso_test`/`iso_test`
with full correctness (`compat_correct`, `merge0_correct`, `merge0_inv`,
`merge_conv_merge0`, `pr_iso_test_rec_correct`, `pr_iso_test_correct`,
`iso_correct`), the improper isomorphisms `is_Iso`/`is_iso`/`iso_fgraph` (`≃`)
with `iso_fgraph_refl`/`iso_fgraph_trans`, and the `quasi_order (≃)`
interpretation with `∈ₛ`/`⊆ₛ`/`=ₛ`.

Deliberately collapsed: Isabelle's four-stage refinement
`pr_iso_test0`/`pr_iso_test1`/`pr_iso_test2`/`pr_iso_test_rec` is proved in one
induction (`pr_iso_test_rec_correct`); the intermediate functions and their
conversion lemmas are not separate definitions.  Their roles are played by
`mapOf (zip …)` (the abstract map) together with `mapOf_zip_submap`,
`injOn_mapOf`, `mapLe`/`mapAdd` lemmas (`mapAdd_le_mapE`, `mapAdd_le_mapI`,
`map_compatI`, `injOn_mapAdd` — the latter subsumes `inj_on_map_add_Un`).

Skipped (not needed downstream; no obstruction expected):
- `pr_iso_same_no_faces` (needs card-of-quotient bookkeeping),
- `equiv_EqF`, `singleton_list_cong_eq_iff`, `Collect_congs_eq_iff`
  (quotient-based; superseded by the class-free translation),
- `pr_Hom_pres_face_nodes` (inlined into `pr_Hom_pres_nodes`),
- `image_image_id_if` (ported only for `rev`: `reverse_image_reverse_image`).

- The bounded existentials `∃F₂ ∈ set Fs₂` / `∃n < length F₂` in the
  executable tests are compiled to `List.any` over `Fs₂` resp.
  `List.range F₂.length`; `compat`/`merge` use `==` (`BEq`) for the
  executable equality tests Isabelle writes with `=`.
-/
import Kepler.Graphs.RotationLemmas
import Kepler.Graphs.QuasiOrder
import Mathlib.Data.List.Rotate
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice

namespace Kepler.Graphs

variable {α β γ : Type _}

/-- PlaneGraphIso.thy: `'a fgraph = 'a list list`. -/
abbrev fgraph (α : Type _) := List (List α)

/-- PlaneGraphIso.thy: `'a Fgraph = 'a list set`. -/
abbrev Fgraph (α : Type _) := Set (List α)

section CongExtras

/-- Injectivity of `map f` under pointwise injectivity on the members.
(Isabelle's `map_inj_on`, with `inj_on f (set l₁ ∪ set l₂)` unfolded.) -/
theorem map_inj_on {f : α → β} {l₁ l₂ : List α}
    (hinj : ∀ a₁ ∈ l₁, ∀ a₂ ∈ l₂, f a₁ = f a₂ → a₁ = a₂)
    (h : l₁.map f = l₂.map f) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact (List.map_eq_nil_iff.mp h.symm).symm
  | cons a as ih =>
    cases l₂ with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hb, hbs⟩ := h
      have hab : a = b := hinj a (by simp) b (by simp) hb
      subst hab
      rw [ih (fun a₁ h₁ a₂ h₂ hh =>
        hinj a₁ (List.mem_cons_of_mem _ h₁) a₂ (List.mem_cons_of_mem _ h₂) hh) hbs]

/-- PlaneGraphIso.thy: `list_cong_rev_iff` -/
theorem list_cong_rev_iff {xs ys : List α} : cong xs.reverse ys.reverse ↔ cong xs ys := by
  constructor
  · rintro ⟨n, h⟩
    exact ⟨xs.length - n % xs.length, by
      rw [← List.reverse_reverse ys, h, List.reverse_rotate, List.reverse_reverse,
        List.length_reverse]⟩
  · rintro ⟨n, h⟩
    exact ⟨xs.length - n % xs.length, by rw [h, List.reverse_rotate]⟩

/-- PlaneGraphIso.thy: `congs_map_eq_iff` (injectivity hypothesis unfolded). -/
theorem cong_map_eq_iff {f : α → β} {xs ys : List α}
    (hinj : ∀ a₁ ∈ xs, ∀ a₂ ∈ ys, f a₁ = f a₂ → a₁ = a₂) :
    cong (xs.map f) (ys.map f) ↔ cong xs ys := by
  constructor
  · rintro ⟨n, h⟩
    refine ⟨n, map_inj_on (f := f) (l₁ := ys) (l₂ := xs.rotate n) ?_ ?_⟩
    · intro a₁ h₁ a₂ h₂ hh
      exact (hinj a₂ (List.mem_rotate.mp h₂) a₁ h₁ hh.symm).symm
    · exact h.trans (List.map_rotate f xs n).symm
  · exact cong_map f

end CongExtras

section HomIso

/-- PlaneGraphIso.thy: `is_pr_Hom`.  Translation of
`(map φ ` Fs₁)//{≅} = Fs₂//{≅}`, unfolded to the class-free characterization
described in the file header. -/
def is_pr_Hom (φ : α → β) (Fs₁ : Fgraph α) (Fs₂ : Fgraph β) : Prop :=
  (∀ F ∈ Fs₁, ∃ F' ∈ Fs₂, cong (F.map φ) F') ∧ (∀ F' ∈ Fs₂, ∃ F ∈ Fs₁, cong (F.map φ) F')

/-- PlaneGraphIso.thy: `is_pr_Iso`. -/
def is_pr_Iso (φ : α → β) (Fs₁ : Fgraph α) (Fs₂ : Fgraph β) : Prop :=
  is_pr_Hom φ Fs₁ Fs₂ ∧ Set.InjOn φ (⋃ F ∈ Fs₁, {v | v ∈ F})

/-- PlaneGraphIso.thy: `is_pr_iso` (`is_pr_Iso` on `set Fs₁`, `set Fs₂`). -/
def is_pr_iso (φ : α → β) (Fs₁ : fgraph α) (Fs₂ : fgraph β) : Prop :=
  is_pr_Iso φ {F | F ∈ Fs₁} {F | F ∈ Fs₂}

/-- PlaneGraphIso.thy: `inj_on (λxs. {xs}//{≅}) (set Fs)`, in class-free form:
no two distinct members of `Fs` are congruent. -/
def noncong (Fs : fgraph α) : Prop := ∀ F₁ ∈ Fs, ∀ F₂ ∈ Fs, cong F₁ F₂ → F₁ = F₂

/-- PlaneGraphIso.thy: `is_pr_Hom_trans` -/
theorem is_pr_Hom_trans {f : α → β} {g : β → γ} {A : Fgraph α} {B : Fgraph β} {C : Fgraph γ}
    (hf : is_pr_Hom f A B) (hg : is_pr_Hom g B C) : is_pr_Hom (g ∘ f) A C := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  constructor
  · intro F hF
    obtain ⟨Fb, hFb, hc⟩ := hf1 F hF
    obtain ⟨Fc, hFc, hc'⟩ := hg1 Fb hFb
    exact ⟨Fc, hFc, cong_trans (by simpa [List.map_map] using cong_map g hc) hc'⟩
  · intro Fc hFc
    obtain ⟨Fb, hFb, hc⟩ := hg2 Fc hFc
    obtain ⟨Fa, hFa, hc'⟩ := hf2 Fb hFb
    exact ⟨Fa, hFa, cong_trans (by simpa [List.map_map] using cong_map g hc') hc⟩

/-- PlaneGraphIso.thy: `is_pr_Hom_rev` -/
theorem is_pr_Hom_rev {φ : α → β} {A : Fgraph α} {B : Fgraph β}
    (h : is_pr_Hom φ A B) : is_pr_Hom φ (List.reverse '' A) (List.reverse '' B) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · rintro F ⟨F₀, hF₀, rfl⟩
    obtain ⟨F', hF', hc⟩ := h1 F₀ hF₀
    exact ⟨F'.reverse, ⟨F', hF', rfl⟩, by
      rw [List.map_reverse]; exact list_cong_rev_iff.mpr hc⟩
  · rintro F' ⟨F'₀, hF'₀, rfl⟩
    obtain ⟨F, hF, hc⟩ := h2 F'₀ hF'₀
    exact ⟨F.reverse, ⟨F, hF, rfl⟩, by
      rw [List.map_reverse]; exact list_cong_rev_iff.mpr hc⟩

/-- PlaneGraphIso.thy: `pr_Hom_pres_nodes` -/
theorem pr_Hom_pres_nodes {φ : α → β} {Fs₁ : Fgraph α} {Fs₂ : Fgraph β}
    (h : is_pr_Hom φ Fs₁ Fs₂) :
    φ '' (⋃ F ∈ Fs₁, {v | v ∈ F}) = ⋃ F ∈ Fs₂, {v | v ∈ F} := by
  obtain ⟨h1, h2⟩ := h
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hv ⊢
    obtain ⟨F, hF, hvF⟩ := hv
    obtain ⟨F', hF', hc⟩ := h1 F hF
    exact ⟨F', hF', (cong_mem hc).mp (List.mem_map_of_mem hvF)⟩
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨F', hF', hxF'⟩ := hx
    obtain ⟨F, hF, hc⟩ := h2 F' hF'
    have hxm : x ∈ F.map φ := (cong_mem hc).mpr hxF'
    obtain ⟨v, hvF, rfl⟩ := List.mem_map.mp hxm
    exact ⟨v, by simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨F, hF, hvF⟩, rfl⟩

/-- Node set of a face-set is unchanged by reversing every face. -/
theorem biUnion_reverse_image (G : Fgraph α) :
    (⋃ F ∈ List.reverse '' G, {v | v ∈ F}) = ⋃ F ∈ G, {v | v ∈ F} := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨F, ⟨F₀, hF₀, rfl⟩, hv⟩
    exact ⟨F₀, hF₀, List.mem_reverse.mp hv⟩
  · rintro ⟨F, hF, hv⟩
    exact ⟨F.reverse, ⟨F, hF, rfl⟩, List.mem_reverse.mpr hv⟩

/-- PlaneGraphIso.thy: `image_image_id_if` for `rev`. -/
theorem reverse_image_reverse_image (G : Fgraph α) :
    List.reverse '' (List.reverse '' G) = G := by
  rw [Set.image_image]
  ext F
  constructor
  · rintro ⟨F₀, hF₀, h⟩
    simp only [List.reverse_reverse] at h
    rw [← h]; exact hF₀
  · intro hF
    exact ⟨F, hF, by simp⟩

/-- Composition of proper isomorphisms (auxiliary for `iso_fgraph_trans`). -/
theorem is_pr_Iso_trans {φ : α → β} {φ' : β → γ} {A : Fgraph α} {B : Fgraph β} {C : Fgraph γ}
    (hφ : is_pr_Iso φ A B) (hφ' : is_pr_Iso φ' B C) : is_pr_Iso (φ' ∘ φ) A C := by
  obtain ⟨hH, hinj⟩ := hφ
  obtain ⟨hH', hinj'⟩ := hφ'
  refine ⟨is_pr_Hom_trans hH hH', ?_⟩
  apply hinj'.comp hinj
  intro x hx
  have hxim : φ x ∈ φ '' (⋃ F ∈ A, {v | v ∈ F}) := Set.mem_image_of_mem φ hx
  rwa [pr_Hom_pres_nodes hH] at hxim


/-- PlaneGraphIso.thy: `is_Hom_distinct`. -/
theorem is_Hom_distinct {φ : α → β} {Fs₁ : Fgraph α} {Fs₂ : Fgraph β}
    (h : is_pr_Hom φ Fs₁ Fs₂) (_hd1 : ∀ F ∈ Fs₁, F.Nodup) (_hd2 : ∀ F ∈ Fs₂, F.Nodup) :
    ∀ F ∈ Fs₁, (F.map φ).Nodup := by
  intro F hF
  obtain ⟨F', hF', hc⟩ := h.1 F hF
  exact (cong_distinct hc).mpr (_hd2 F' hF')

/-- PlaneGraphIso.thy: `pr_iso_same_no_nodes` (with `Set.ncard`; no finiteness
hypothesis is needed since `ncard` of an infinite set is `0`). -/
theorem pr_iso_same_no_nodes {φ : α → β} {Fs₁ : fgraph α} {Fs₂ : fgraph β}
    (h : is_pr_iso φ Fs₁ Fs₂) :
    (⋃ F ∈ {F | F ∈ Fs₁}, {v | v ∈ F}).ncard =
      (⋃ F ∈ {F | F ∈ Fs₂}, {v | v ∈ F}).ncard := by
  obtain ⟨hH, hinj⟩ := h
  rw [← pr_Hom_pres_nodes hH]
  exact hinj.ncard_image.symm

end HomIso

section ImproperIso

/-- PlaneGraphIso.thy: `is_Iso` (improper isomorphisms: proper, or proper onto
the reversed faces). -/
def is_Iso (φ : α → β) (Fs₁ : Fgraph α) (Fs₂ : Fgraph β) : Prop :=
  is_pr_Iso φ Fs₁ Fs₂ ∨ is_pr_Iso φ Fs₁ (List.reverse '' Fs₂)

/-- PlaneGraphIso.thy: `is_iso`. -/
def is_iso (φ : α → β) (Fs₁ : fgraph α) (Fs₂ : fgraph β) : Prop :=
  is_Iso φ {F | F ∈ Fs₁} {F | F ∈ Fs₂}

/-- PlaneGraphIso.thy: `iso_fgraph` (`≃`). -/
def iso_fgraph (g₁ g₂ : fgraph α) : Prop := ∃ φ, is_iso φ g₁ g₂

/-- PlaneGraphIso.thy: `≃` on fgraphs. -/
scoped infixl:60 " ≃ " => Kepler.Graphs.iso_fgraph

/-- PlaneGraphIso.thy: `iso_fgraph_refl` -/
theorem iso_fgraph_refl (g : fgraph α) : iso_fgraph g g := by
  refine ⟨id, Or.inl ⟨?_, Set.injOn_id _⟩⟩
  constructor
  · intro F hF; exact ⟨F, hF, by simpa using cong_refl F⟩
  · intro F hF; exact ⟨F, hF, by simpa using cong_refl F⟩

/-- PlaneGraphIso.thy: `iso_fgraph_trans` -/
theorem iso_fgraph_trans {f g h : fgraph α} (hfg : f ≃ g) (hgh : g ≃ h) : f ≃ h := by
  obtain ⟨φ, hφ⟩ := hfg
  obtain ⟨φ', hφ'⟩ := hgh
  unfold is_iso is_Iso at hφ hφ'
  rcases hφ with hφ | hφ <;> rcases hφ' with hφ' | hφ'
  · exact ⟨φ' ∘ φ, Or.inl (is_pr_Iso_trans hφ hφ')⟩
  · exact ⟨φ' ∘ φ, Or.inr (is_pr_Iso_trans hφ hφ')⟩
  · -- φ : f → rev '' g, φ' : g → h
    have hH : is_pr_Hom (φ' ∘ φ) {F | F ∈ f} (List.reverse '' {F | F ∈ h}) :=
      is_pr_Hom_trans hφ.1 (is_pr_Hom_rev hφ'.1)
    have hinj : Set.InjOn (φ' ∘ φ) (⋃ F ∈ {F | F ∈ f}, {v | v ∈ F}) := by
      apply hφ'.2.comp hφ.2
      intro x hx
      have hxim : φ x ∈ φ '' (⋃ F ∈ {F | F ∈ f}, {v | v ∈ F}) := Set.mem_image_of_mem φ hx
      rw [pr_Hom_pres_nodes hφ.1, biUnion_reverse_image] at hxim
      exact hxim
    exact ⟨φ' ∘ φ, Or.inr ⟨hH, hinj⟩⟩
  · -- φ : f → rev '' g, φ' : g → rev '' h
    have h1 : is_pr_Hom φ' (List.reverse '' {F | F ∈ g}) {F | F ∈ h} := by
      have hh := is_pr_Hom_rev hφ'.1
      rwa [reverse_image_reverse_image] at hh
    have hinj : Set.InjOn (φ' ∘ φ) (⋃ F ∈ {F | F ∈ f}, {v | v ∈ F}) := by
      apply hφ'.2.comp hφ.2
      intro x hx
      have hxim : φ x ∈ φ '' (⋃ F ∈ {F | F ∈ f}, {v | v ∈ F}) := Set.mem_image_of_mem φ hx
      rw [pr_Hom_pres_nodes hφ.1, biUnion_reverse_image] at hxim
      exact hxim
    exact ⟨φ' ∘ φ, Or.inl ⟨is_pr_Hom_trans hφ.1 h1, hinj⟩⟩

/-- PlaneGraphIso.thy: interpretation `qle_gr : quasi_order (≃)`. -/
theorem quasiOrder_iso_fgraph : QuasiOrder (iso_fgraph (α := α)) :=
  ⟨iso_fgraph_refl, fun _ _ _ => iso_fgraph_trans⟩

/-- PlaneGraphIso.thy: `qle_gr.in_qle` (`∈ₛ`). -/
def inIso (x : fgraph α) (M : Set (fgraph α)) : Prop := inQle iso_fgraph x M

/-- PlaneGraphIso.thy: `qle_gr.subseteq_qle` (`⊆ₛ`). -/
def subsetIso (M N : Set (fgraph α)) : Prop := subseteqQle iso_fgraph M N

/-- PlaneGraphIso.thy: `qle_gr.seteq_qle` (`=ₛ`). -/
def seteqIso (M N : Set (fgraph α)) : Prop := seteqQle iso_fgraph M N

/-- `∈ₛ` from PlaneGraphIso.thy. -/
scoped infix:60 " ∈ₛ " => Kepler.Graphs.inIso
/-- `⊆ₛ` from PlaneGraphIso.thy. -/
scoped infix:60 " ⊆ₛ " => Kepler.Graphs.subsetIso
/-- `=ₛ` from PlaneGraphIso.thy. -/
scoped infix:60 " =ₛ " => Kepler.Graphs.seteqIso

end ImproperIso


/-- Node-set of a cons fgraph, as a union (auxiliary for `is_iso_Cons` and
the correctness proofs). -/
theorem biUnion_cons_setOf (F₁ : List α) (Fs₁ : fgraph α) :
    (⋃ F ∈ {F | F ∈ F₁ :: Fs₁}, {v | v ∈ F}) =
      {v | v ∈ F₁} ∪ ⋃ F ∈ {F | F ∈ Fs₁}, {v | v ∈ F} := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨F, hF, hv⟩
    rcases List.mem_cons.mp hF with rfl | hF
    · exact Or.inl hv
    · exact Or.inr ⟨F, hF, hv⟩
  · rintro (hv | ⟨F, hF, hv⟩)
    · exact ⟨F₁, List.mem_cons_self, hv⟩
    · exact ⟨F, List.mem_cons_of_mem _ hF, hv⟩

section IsoCons

variable [BEq β] [LawfulBEq β]

/-- PlaneGraphIso.thy: `is_iso_Cons` (proved directly from the definitions;
it subsumes Isabelle's `is_pr_Iso_rec` detour through set difference). -/
theorem is_iso_Cons {φ : α → β} {F₁ : List α} {Fs₁' : fgraph α} {Fs₂ : fgraph β}
    (hdist1 : (F₁ :: Fs₁').Nodup) (hdist2 : Fs₂.Nodup)
    (hnc1 : noncong (F₁ :: Fs₁')) (hnc2 : noncong Fs₂) :
    is_pr_iso φ (F₁ :: Fs₁') Fs₂ ↔
      ∃ F₂ ∈ Fs₂, F₁.length = F₂.length ∧ is_pr_iso φ Fs₁' (Fs₂.erase F₂) ∧
        (∃ n, F₁.map φ = F₂.rotate n) ∧
        Set.InjOn φ ({v | v ∈ F₁} ∪ ⋃ F ∈ {F | F ∈ Fs₁'}, {v | v ∈ F}) := by
  constructor
  · rintro ⟨hH, hinj⟩
    obtain ⟨hH1, hH2⟩ := hH
    obtain ⟨F₂, hF₂, hc⟩ := hH1 F₁ (List.mem_cons_self)
    have hlen : F₁.length = F₂.length := by
      have hl := cong_length hc
      rwa [List.length_map] at hl
    refine ⟨F₂, hF₂, hlen, ?_, cong_sym hc, ?_⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro F hF
        obtain ⟨F', hF', hc'⟩ := hH1 F (List.mem_cons_of_mem _ hF)
        have hne : F' ≠ F₂ := by
          intro heq
          subst heq
          have hcc : cong (F.map φ) (F₁.map φ) := cong_trans hc' (cong_sym hc)
          have hcF : cong F F₁ := (cong_map_eq_iff (f := φ) (fun a₁ h₁ a₂ h₂ hh =>
            hinj (Set.mem_biUnion (List.mem_cons_of_mem _ hF) h₁)
              (Set.mem_biUnion (List.mem_cons_self) h₂) hh)).mp hcc
          have hFF : F = F₁ :=
            hnc1 F (List.mem_cons_of_mem _ hF) F₁ (List.mem_cons_self) hcF
          subst hFF
          exact (List.nodup_cons.mp hdist1).1 hF
        exact ⟨F', (List.mem_erase_of_ne hne).mpr hF', hc'⟩
      · intro F' hF'
        have hF'm : F' ∈ Fs₂ := List.mem_of_mem_erase hF'
        obtain ⟨F, hF, hc'⟩ := hH2 F' hF'm
        have hFne : F ≠ F₁ := by
          intro heq
          subst heq
          have hcc : cong F' F₂ := cong_trans (cong_sym hc') hc
          have hFF : F' = F₂ := hnc2 F' hF'm F₂ hF₂ hcc
          subst hFF
          exact hdist2.not_mem_erase hF'
        exact ⟨F, (List.mem_cons.mp hF).resolve_left hFne, hc'⟩
      · refine Set.InjOn.mono ?_ hinj
        intro x hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
        obtain ⟨F, hF, hxF⟩ := hx
        exact ⟨F, List.mem_cons_of_mem _ hF, hxF⟩
    · rw [← biUnion_cons_setOf]; exact hinj
  · rintro ⟨F₂, hF₂, hlen, hiso, ⟨n, hn⟩, hinj⟩
    obtain ⟨hH, -⟩ := hiso
    obtain ⟨hH1, hH2⟩ := hH
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨F₂, hF₂, cong_sym ⟨n, hn⟩⟩
      · obtain ⟨F', hF', hc⟩ := hH1 F hF
        exact ⟨F', List.mem_of_mem_erase hF', hc⟩
    · intro F' hF'
      by_cases hcase : F' ∈ Fs₂.erase F₂
      · obtain ⟨F, hF, hc⟩ := hH2 F' hcase
        exact ⟨F, List.mem_cons_of_mem _ hF, hc⟩
      · have hFF : F' = F₂ := by
          by_contra hne
          exact hcase ((List.mem_erase_of_ne hne).mpr hF')
        subst hFF
        exact ⟨F₁, List.mem_cons_self, cong_sym ⟨n, hn⟩⟩
    · rw [biUnion_cons_setOf]; exact hinj

end IsoCons


section MapLayer

/-- Isabelle's partial maps `'a ⇀ 'b` as functions into `Option`.
`map_of`: earlier entries override later ones
(Isabelle: `map_of ((x,y)#ps) = (map_of ps)(x ↦ y)`). -/
def mapOf [DecidableEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: ps, z => if z = x then some y else mapOf ps z

@[simp] theorem mapOf_nil [DecidableEq α] (x : α) :
    mapOf ([] : List (α × β)) x = none := rfl

theorem mapOf_cons [DecidableEq α] (a : α) (b : β) (ps : List (α × β)) (x : α) :
    mapOf ((a, b) :: ps) x = if x = a then some b else mapOf ps x := rfl

/-- Isabelle's `dom m`. -/
def mapDom (m : α → Option β) : Set α := {x | (m x).isSome}

/-- Isabelle's `f ⊆ₘ g` (`map_le`). -/
def mapLe (m m' : α → Option β) : Prop := ∀ x ∈ mapDom m, m x = m' x

/-- Isabelle's `m ++ m'` (`map_add`, right-biased). -/
def mapAdd (m m' : α → Option β) : α → Option β := fun x =>
  match m' x with
  | some v => some v
  | none => m x

theorem mapAdd_apply (m m' : α → Option β) (x : α) :
    mapAdd m m' x = (match m' x with | some v => some v | none => m x) := rfl

theorem mapAdd_eq_left {m m' : α → Option β} {x : α} (h : m' x = none) :
    mapAdd m m' x = m x := by rw [mapAdd_apply, h]

theorem mapAdd_eq_right {m m' : α → Option β} {x : α} {v : β} (h : m' x = some v) :
    mapAdd m m' x = some v := by rw [mapAdd_apply, h]

/-- `dom (m ++ m') = dom m ∪ dom m'`. -/
theorem mapAdd_dom {m m' : α → Option β} : mapDom (mapAdd m m') = mapDom m ∪ mapDom m' := by
  ext x
  cases hx' : m' x with
  | none => simp [mapDom, mapAdd_eq_left hx', hx']
  | some v => simp [mapDom, mapAdd_eq_right hx', hx']

theorem mapLe_trans {m₁ m₂ m₃ : α → Option β} (h₁ : mapLe m₁ m₂) (h₂ : mapLe m₂ m₃) :
    mapLe m₁ m₃ := by
  intro x hx
  have e1 := h₁ x hx
  have hx2 : x ∈ mapDom m₂ := by
    rw [mapDom, Set.mem_setOf_eq] at hx ⊢
    rwa [e1] at hx
  exact e1.trans (h₂ x hx2)

/-- Isabelle's `map_add_le_mapE`. -/
theorem mapAdd_le_mapE {m m' h : α → Option β} (hl : mapLe (mapAdd m m') h) : mapLe m' h := by
  intro x hx
  cases hx' : m' x with
  | none => simp [mapDom, hx'] at hx
  | some v =>
    have e := hl x (by rw [mapDom, Set.mem_setOf_eq, mapAdd_eq_right hx']; rfl)
    rw [mapAdd_eq_right hx'] at e
    exact e

/-- Isabelle's `map_add_le_mapI`. -/
theorem mapAdd_le_mapI {m m' h : α → Option β} (hl : mapLe m h) (hr : mapLe m' h) :
    mapLe (mapAdd m m') h := by
  intro x hx
  cases hx' : m' x with
  | some v =>
    rw [mapAdd_eq_right hx', ← hx']
    exact hr x (by rw [mapDom, Set.mem_setOf_eq, hx']; rfl)
  | none =>
    rw [mapAdd_eq_left hx']
    apply hl x
    rw [mapAdd_dom] at hx
    rcases hx with hx | hx
    · exact hx
    · simp [mapDom, hx'] at hx

/-- Isabelle's `map_compatI`. -/
theorem map_compatI {m m' : α → Option β} {h : α → β} (hl : mapLe m (some ∘ h))
    (hr : mapLe m' (some ∘ h)) : mapLe m (mapAdd m m') := by
  intro x hx
  cases hx' : m' x with
  | none => exact (mapAdd_eq_left hx').symm
  | some v =>
    have e1 := hr x (by rw [mapDom, Set.mem_setOf_eq, hx']; rfl)
    have e2 := hl x hx
    rw [hx'] at e1
    rw [mapAdd_eq_right hx']
    exact e2.trans e1.symm

/-- Isabelle's `inj_on_map_add_Un` (strengthened: the individual `inj_on`
hypotheses are unnecessary). -/
theorem injOn_mapAdd {m m' : α → Option β} {f : α → β}
    (hl : mapLe m (some ∘ f)) (hr : mapLe m' (some ∘ f))
    (hf : Set.InjOn f (mapDom m' ∪ mapDom m)) :
    Set.InjOn (mapAdd m m') (mapDom m' ∪ mapDom m) := by
  have key : ∀ x ∈ mapDom m' ∪ mapDom m, mapAdd m m' x = some (f x) := by
    intro x hx
    rcases hx with hx | hx
    · cases hx' : m' x with
      | none => simp [mapDom, hx'] at hx
      | some v =>
        have e := hr x hx
        rw [hx'] at e
        rw [mapAdd_eq_right hx']
        exact e
    · cases hx' : m' x with
      | some v =>
        have e := hr x (by rw [mapDom, Set.mem_setOf_eq, hx']; rfl)
        rw [hx'] at e
        rw [mapAdd_eq_right hx']
        exact e
      | none =>
        rw [mapAdd_eq_left hx']
        exact hl x hx
  intro x hx y hy hxy
  rw [key x hx, key y hy] at hxy
  exact hf hx hy (Option.some.inj hxy)

/-- Isabelle's `map_of_zip_eq_SomeD` variant: membership form, no distinctness
needed. -/
theorem mem_of_mapOf_eq_some [DecidableEq α] {ps : List (α × β)} {x : α} {y : β} :
    mapOf ps x = some y → (x, y) ∈ ps := by
  induction ps with
  | nil => simp [mapOf]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : x = a
    · subst h
      rw [mapOf_cons, if_pos rfl]
      intro hh
      exact List.mem_cons.mpr (Or.inl (by rw [Option.some.inj hh]))
    · rw [mapOf_cons, if_neg h]
      intro hh
      exact List.mem_cons.mpr (Or.inr (ih hh))

/-- With distinct keys, `mapOf` lookup is exactly list membership. -/
theorem mapOf_eq_some_iff [DecidableEq α] {ps : List (α × β)}
    (hd : (ps.map Prod.fst).Nodup) {x : α} {y : β} :
    mapOf ps x = some y ↔ (x, y) ∈ ps := by
  induction ps with
  | nil => simp [mapOf]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    have hd' : (ps.map Prod.fst).Nodup := (List.nodup_cons.mp hd).2
    have ha : a ∉ ps.map Prod.fst := (List.nodup_cons.mp hd).1
    by_cases h : x = a
    · subst h
      rw [mapOf_cons, if_pos rfl]
      constructor
      · intro hh
        exact List.mem_cons.mpr (Or.inl (by rw [Option.some.inj hh]))
      · intro hh
        rcases List.mem_cons.mp hh with hh | hh
        · obtain ⟨-, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp hh
          rfl
        · exact absurd (List.mem_map_of_mem hh) ha
    · rw [mapOf_cons, if_neg h]
      constructor
      · intro hh
        exact List.mem_cons.mpr (Or.inr ((ih hd').mp hh))
      · intro hh
        rcases List.mem_cons.mp hh with hh | hh
        · exact absurd (congrArg Prod.fst hh) h
        · exact (ih hd').mpr hh

/-- The domain of `mapOf ps` is the set of first components. -/
theorem isSome_mapOf_iff [DecidableEq α] (ps : List (α × β)) (x : α) :
    (mapOf ps x).isSome ↔ x ∈ ps.map Prod.fst := by
  induction ps with
  | nil => simp [mapOf]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : x = a
    · subst h
      simp [mapOf_cons]
    · simp [mapOf_cons, h, ih]

/-- Auxiliary: the first component is determined by the second when the
seconds are distinct. -/
theorem fst_inj_of_nodup_snd {ps : List (α × β)} (hd : (ps.map Prod.snd).Nodup)
    {x y : α} {a : β} (hx : (x, a) ∈ ps) (hy : (y, a) ∈ ps) : x = y := by
  induction ps with
  | nil => simp at hx
  | cons p ps ih =>
    obtain ⟨c, d⟩ := p
    have hd' : (ps.map Prod.snd).Nodup := (List.nodup_cons.mp hd).2
    have hcd : d ∉ ps.map Prod.snd := (List.nodup_cons.mp hd).1
    rcases List.mem_cons.mp hx with hx | hx
    · rcases List.mem_cons.mp hy with hy | hy
      · exact congrArg Prod.fst (hx.trans hy.symm)
      · have had : a = d := congrArg Prod.snd hx
        have h2 : a ∈ ps.map Prod.snd := List.mem_map_of_mem hy
        exact absurd (had ▸ h2) hcd
    · rcases List.mem_cons.mp hy with hy | hy
      · have had : a = d := congrArg Prod.snd hy
        have h2 : a ∈ ps.map Prod.snd := List.mem_map_of_mem hx
        exact absurd (had ▸ h2) hcd
      · exact ih hd' hx hy

/-- Isabelle's `[simp]` lemma `distinct(map snd xys) ⟹ inj_on (map_of xys)
(dom (map_of xys))`. -/
theorem injOn_mapOf [DecidableEq α] {ps : List (α × β)}
    (hd : (ps.map Prod.snd).Nodup) : Set.InjOn (mapOf ps) (mapDom (mapOf ps)) := by
  intro x hx y hy hxy
  rw [mapDom, Set.mem_setOf_eq] at hx
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hx
  rw [ha] at hxy
  exact fst_inj_of_nodup_snd hd (mem_of_mapOf_eq_some ha) (mem_of_mapOf_eq_some hxy.symm)

/-- Isabelle's `map_upd_submap` inlined into an induction:
`map_of_zip_submap`. -/
theorem mapOf_zip_submap [DecidableEq α] {xs : List α} {ys : List β} {f : α → β}
    (hlen : xs.length = ys.length) (hd : xs.Nodup) :
    mapLe (mapOf (xs.zip ys)) (some ∘ f) ↔ xs.map f = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [mapLe, mapDom]
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hd' : xs.Nodup := (List.nodup_cons.mp hd).2
      have hx : x ∉ xs := (List.nodup_cons.mp hd).1
      have hstep : mapLe (mapOf ((x, y) :: xs.zip ys)) (some ∘ f) ↔
          f x = y ∧ mapLe (mapOf (xs.zip ys)) (some ∘ f) := by
        constructor
        · intro h
          constructor
          · have hxd : x ∈ mapDom (mapOf ((x, y) :: xs.zip ys)) := by
              rw [mapDom, Set.mem_setOf_eq, mapOf_cons, if_pos rfl]
              rfl
            have e := h x hxd
            rw [mapOf_cons, if_pos rfl] at e
            exact (Option.some.inj e).symm
          · intro z hz
            have hmem : z ∈ xs := by
              have hm := (isSome_mapOf_iff (xs.zip ys) z).mp hz
              rwa [List.map_fst_zip (by omega)] at hm
            have hzx : z ≠ x := fun he => hx (he ▸ hmem)
            have hz' : z ∈ mapDom (mapOf ((x, y) :: xs.zip ys)) := by
              rw [mapDom, Set.mem_setOf_eq] at hz ⊢
              rw [mapOf_cons, if_neg hzx]
              exact hz
            have e := h z hz'
            rwa [mapOf_cons, if_neg hzx] at e
        · rintro ⟨h1, h2⟩
          intro z hz
          by_cases hzx : z = x
          · subst hzx
            rw [mapOf_cons, if_pos rfl, ← h1]
            rfl
          · rw [mapOf_cons, if_neg hzx]
            apply h2
            rw [mapDom, Set.mem_setOf_eq] at hz ⊢
            rw [mapOf_cons, if_neg hzx] at hz
            exact hz
      rw [List.zip_cons_cons, List.map_cons, List.cons.injEq, hstep, ih hlen hd']

theorem mapOf_append [DecidableEq α] (l₁ l₂ : List (α × β)) (x : α) :
    mapOf (l₁ ++ l₂) x = mapAdd (mapOf l₂) (mapOf l₁) x := by
  induction l₁ with
  | nil => simp [mapAdd_apply]
  | cons p l₁ ih =>
    obtain ⟨a, b⟩ := p
    rw [List.cons_append, mapOf_cons, mapAdd_apply, mapOf_cons]
    by_cases h : x = a
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      rw [ih, mapAdd_apply]

end MapLayer


section CompatMerge

/-- PlaneGraphIso.thy: `oneone` (`distinct (map fst xys) ∧ distinct (map snd
xys)`). -/
def oneone (xys : List (α × β)) : Prop :=
  (xys.map Prod.fst).Nodup ∧ (xys.map Prod.snd).Nodup

theorem oneone_nil : oneone ([] : List (α × β)) := ⟨List.nodup_nil, List.nodup_nil⟩

/-- PlaneGraphIso.thy: `compat` (`∀(x,y)∈I. ∀(x',y')∈I'. (x = x') = (y = y')`),
with executable equality tests. -/
def compat [BEq α] [BEq β] (I I' : List (α × β)) : Bool :=
  I.all fun p => I'.all fun q => (p.1 == q.1) == (p.2 == q.2)

/-- Boolean equality of equality tests is the iff of the equalities. -/
theorem beq_beq [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (x x' : α) (y y' : β) :
    ((x == x') == (y == y')) = true ↔ (x = x' ↔ y = y') := by
  cases h1 : (x == x') <;> cases h2 : (y == y')
  · rw [beq_eq_false_iff_ne] at h1; rw [beq_eq_false_iff_ne] at h2; simp [h1, h2]
  · rw [beq_eq_false_iff_ne] at h1; rw [beq_iff_eq] at h2; simp [h1, h2]
  · rw [beq_iff_eq] at h1; rw [beq_eq_false_iff_ne] at h2; simp [h1, h2]
  · rw [beq_iff_eq] at h1; rw [beq_iff_eq] at h2; simp [h1, h2]

/-- Propositional reading of `compat`. -/
theorem compat_iff [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (I I' : List (α × β)) :
    compat I' I = true ↔ ∀ p ∈ I', ∀ q ∈ I, (p.1 = q.1 ↔ p.2 = q.2) := by
  simp only [compat, List.all_eq_true]
  constructor
  · intro h p hp q hq
    exact (beq_beq p.1 q.1 p.2 q.2).mp (h p hp q hq)
  · intro h p hp q hq
    exact (beq_beq p.1 q.1 p.2 q.2).mpr (h p hp q hq)

/-- PlaneGraphIso.thy: `compat_correct`. -/
theorem compat_correct [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] [DecidableEq α]
    {I I' : List (α × β)} (hI : oneone I) (hI' : oneone I') :
    compat I' I = true ↔
      mapLe (mapOf I) (mapAdd (mapOf I) (mapOf I')) ∧
        Set.InjOn (mapAdd (mapOf I) (mapOf I')) (mapDom (mapAdd (mapOf I) (mapOf I'))) := by
  rw [compat_iff]
  have eI : ∀ x y, mapOf I x = some y ↔ (x, y) ∈ I := fun _ _ => mapOf_eq_some_iff hI.1
  have eI' : ∀ x y, mapOf I' x = some y ↔ (x, y) ∈ I' := fun _ _ => mapOf_eq_some_iff hI'.1
  constructor
  · intro h
    constructor
    · -- mapLe (mapOf I) (mapAdd (mapOf I) (mapOf I'))
      intro x hx
      rw [mapDom, Set.mem_setOf_eq, isSome_mapOf_iff] at hx
      obtain ⟨⟨a, b⟩, hab, hax⟩ := List.mem_map.mp hx
      have hax' : a = x := hax
      subst hax'
      have hb : mapOf I a = some b := (eI a b).mpr hab
      cases hb' : mapOf I' a with
      | none => rw [mapAdd_eq_left hb']
      | some b' =>
        rw [mapAdd_eq_right hb']
        have hmem' : (a, b') ∈ I' := (eI' a b').mp hb'
        have hbb : b' = b := (h (a, b') hmem' (a, b) hab).mp rfl
        rw [hb, ← hbb]
    · -- InjOn (mapAdd ...) (dom ...)
      intro x hx y hy hxy
      obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp hx
      obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.mp hy
      have key : ∀ z v, mapAdd (mapOf I) (mapOf I') z = some v →
          (z, v) ∈ I' ∨ (z, v) ∈ I := by
        intro z v hv
        cases hz : mapOf I' z with
        | none =>
          rw [mapAdd_eq_left hz] at hv
          exact Or.inr ((eI z v).mp hv)
        | some w =>
          rw [mapAdd_eq_right hz] at hv
          obtain rfl := Option.some.inj hv
          exact Or.inl ((eI' z w).mp hz)
      have hvv : vx = vy := by rw [hvx, hvy] at hxy; exact Option.some.inj hxy
      rcases key x vx hvx with hxv | hxv <;> rcases key y vy hvy with hyv | hyv
      · exact fst_inj_of_nodup_snd hI'.2 hxv (hvv.symm ▸ hyv)
      · exact (h (x, vx) hxv (y, vy) hyv).mpr hvv
      · exact ((h (y, vy) hyv (x, vx) hxv).mpr hvv.symm).symm
      · exact fst_inj_of_nodup_snd hI.2 hxv (hvv.symm ▸ hyv)
  · rintro ⟨hle, hinj⟩
    intro p hp q hq
    obtain ⟨x, y⟩ := p
    obtain ⟨x', y'⟩ := q
    show (x = x' ↔ y = y')
    have hmx : mapOf I' x = some y := (eI' x y).mpr hp
    have hmx' : mapOf I x' = some y' := (eI x' y').mpr hq
    have hx'dom : x' ∈ mapDom (mapOf I) := by
      rw [mapDom, Set.mem_setOf_eq, hmx']; rfl
    have hle' := hle x' hx'dom
    constructor
    · intro hxx
      subst hxx
      have hadd : mapAdd (mapOf I) (mapOf I') x = some y := mapAdd_eq_right hmx
      rw [hadd, hmx'] at hle'
      exact (Option.some.inj hle').symm
    · intro hyy
      have hxdom : x ∈ mapDom (mapAdd (mapOf I) (mapOf I')) := by
        rw [mapAdd_dom]
        exact Or.inr (by rw [mapDom, Set.mem_setOf_eq, hmx]; rfl)
      have hx'dom2 : x' ∈ mapDom (mapAdd (mapOf I) (mapOf I')) := by
        rw [mapAdd_dom]
        exact Or.inl hx'dom
      have haddx : mapAdd (mapOf I) (mapOf I') x = some y := mapAdd_eq_right hmx
      have haddx' : mapAdd (mapOf I) (mapOf I') x' = some y' := by
        rw [← hle']; exact hmx'
      have e : mapAdd (mapOf I) (mapOf I') x = mapAdd (mapOf I) (mapOf I') x' :=
        haddx.trans ((congrArg some hyy).trans haddx'.symm)
      exact hinj hxdom hx'dom2 e

/-- PlaneGraphIso.thy: `merge0` (`[xy ← I'. fst xy ∉ fst ` set I] @ I`).
The filter test `fst xy ∉ fst ` set I` is written as the executable
`I.all (fun q => xy.1 != q.1)`; see `all_bne_not_mem_map_fst`. -/
def merge0 [BEq α] (I' I : List (α × β)) : List (α × β) :=
  (I'.filter fun xy => I.all fun q => xy.1 != q.1) ++ I

/-- The executable filter test agrees with non-membership. -/
theorem all_bne_not_mem_map_fst [BEq α] [LawfulBEq α] {x : α} {I : List (α × β)} :
    (I.all fun q => x != q.1) = true ↔ x ∉ I.map Prod.fst := by
  rw [List.all_eq_true]
  constructor
  · intro hall hx
    obtain ⟨⟨a, b⟩, hab, hax⟩ := List.mem_map.mp hx
    have hax' : a = x := hax
    have h1 := hall (a, b) hab
    rw [hax', bne_self_eq_false] at h1
    exact Bool.false_ne_true h1
  · intro hx q hq
    rw [bne_iff_ne]
    intro he
    exact hx (he.symm ▸ List.mem_map_of_mem hq)

/-- PlaneGraphIso.thy: `merge`. -/
def merge [BEq α] : List (α × β) → List (α × β) → List (α × β)
  | [], I => I
  | (x, y) :: xys, I =>
    if I.all fun q => x != q.1 then (x, y) :: merge xys I else merge xys I

/-- PlaneGraphIso.thy: `merge_conv_merge0`. -/
theorem merge_conv_merge0 [BEq α] (I' I : List (α × β)) :
    merge I' I = merge0 I' I := by
  induction I' with
  | nil => rfl
  | cons p xys ih =>
    obtain ⟨x, y⟩ := p
    cases h : (I.all fun q => x != q.1) <;>
      simp [merge, merge0, h, ih]

/-- `mapOf` of the filtered list is `none` on the domain of `I`. -/
theorem mapOf_filter_all_bne_eq_none [DecidableEq α] [BEq α] [LawfulBEq α]
    {I' I : List (α × β)} {x : α} (hx : x ∈ I.map Prod.fst) :
    mapOf (I'.filter fun xy => I.all fun q => xy.1 != q.1) x = none := by
  cases h : mapOf (I'.filter fun xy => I.all fun q => xy.1 != q.1) x with
  | none => rfl
  | some y =>
    have hmem := mem_of_mapOf_eq_some h
    rw [List.mem_filter] at hmem
    exact absurd hx (all_bne_not_mem_map_fst.mp hmem.2)

/-- `mapOf` of the filtered list agrees with `mapOf I'` off the domain of `I`. -/
theorem mapOf_filter_all_bne [DecidableEq α] [BEq α] [LawfulBEq α]
    {I' I : List (α × β)} {x : α} (hx : x ∉ I.map Prod.fst) :
    mapOf (I'.filter fun xy => I.all fun q => xy.1 != q.1) x = mapOf I' x := by
  induction I' with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases ha : x = a
    · subst ha
      rw [List.filter_cons_of_pos (p := fun xy : α × β => I.all fun q => xy.1 != q.1)
          (all_bne_not_mem_map_fst.mpr hx),
        mapOf_cons, if_pos rfl, mapOf_cons, if_pos rfl]
    · cases hp : (fun xy => I.all fun q => xy.1 != q.1) (a, b) with
      | true =>
        rw [List.filter_cons_of_pos (p := fun xy : α × β => I.all fun q => xy.1 != q.1) hp,
          mapOf_cons, if_neg ha, mapOf_cons, if_neg ha, ih]
      | false =>
        rw [List.filter_cons_of_neg (p := fun xy : α × β => I.all fun q => xy.1 != q.1)
            (by simp [hp]),
          mapOf_cons, if_neg ha, ih]

/-- PlaneGraphIso.thy: `merge0_correct`. -/
theorem merge0_correct [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] [DecidableEq α]
    {I I' : List (α × β)} (hI : oneone I) (hI' : oneone I')
    (hc : compat I' I = true) :
    mapOf (merge0 I' I) = mapAdd (mapOf I) (mapOf I') := by
  funext x
  rw [merge0, mapOf_append, mapAdd_apply]
  by_cases hx : x ∈ I.map Prod.fst
  · have h1 : mapOf (I'.filter fun xy => I.all fun q => xy.1 != q.1) x = none :=
      mapOf_filter_all_bne_eq_none hx
    rw [h1]
    cases hx' : mapOf I' x with
    | none => rw [mapAdd_eq_left hx']
    | some y =>
      rw [mapAdd_eq_right hx']
      have hmem' : (x, y) ∈ I' := (mapOf_eq_some_iff hI'.1).mp hx'
      obtain ⟨⟨a, b'⟩, hab, hax⟩ := List.mem_map.mp hx
      have hax' : a = x := hax
      have hcc := (compat_iff I I').mp hc (x, y) hmem' (a, b') hab
      have hyb : y = b' := hcc.mp hax'.symm
      have hmapI : mapOf I x = some b' := (mapOf_eq_some_iff hI.1).mpr (hax' ▸ hab)
      rw [hmapI, ← hyb]
  · have h1 : mapOf (I'.filter fun xy => I.all fun q => xy.1 != q.1) x =
        mapOf I' x := mapOf_filter_all_bne hx
    rw [h1, ← mapAdd_apply]

/-- PlaneGraphIso.thy: `merge0_inv`. -/
theorem merge0_inv [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {I I' : List (α × β)} (hI : oneone I) (hI' : oneone I')
    (hc : compat I' I = true) :
    oneone (merge0 I' I) := by
  obtain ⟨hIf, hIs⟩ := hI
  obtain ⟨hI'f, hI's⟩ := hI'
  have hcomp := (compat_iff I I').mp hc
  simp only [merge0, oneone, List.map_append]
  constructor
  · rw [List.nodup_append]
    refine ⟨hI'f.sublist (List.Sublist.map _ List.filter_sublist), hIf, ?_⟩
    intro a ha b hb hab
    obtain ⟨⟨a₁, b₁⟩, hab₁, hfa⟩ := List.mem_map.mp ha
    have hfa' : a₁ = a := hfa
    rw [List.mem_filter] at hab₁
    -- hab₁.2 : the all-bne test on a₁ is true → a₁ ∉ map fst I
    have hnotin := all_bne_not_mem_map_fst.mp hab₁.2
    -- b ∈ map fst I and a = b → a₁ ∈ map fst I
    rw [← hab, ← hfa'] at hb
    exact absurd hb hnotin
  · rw [List.nodup_append]
    refine ⟨hI's.sublist (List.Sublist.map _ List.filter_sublist), hIs, ?_⟩
    intro a ha b hb hab
    obtain ⟨⟨x₁, y₁⟩, h₁, hfa⟩ := List.mem_map.mp ha
    obtain ⟨⟨x₂, y₂⟩, h₂, hfb⟩ := List.mem_map.mp hb
    have hfa' : y₁ = a := hfa
    have hfb' : y₂ = b := hfb
    rw [List.mem_filter] at h₁
    have hnotin := all_bne_not_mem_map_fst.mp h₁.2
    -- compat on (x₁,y₁) ∈ I' and (x₂,y₂) ∈ I with y₁ = a = b = y₂ gives x₁ = x₂
    have hxx : x₁ = x₂ :=
      (hcomp (x₁, y₁) h₁.1 (x₂, y₂) h₂).mpr (hfa'.trans (hab.trans hfb'.symm))
    -- then x₁ ∈ map fst I, contradicting the filter test
    have hmem2 : x₂ ∈ I.map Prod.fst := List.mem_map_of_mem h₂
    exact absurd (hxx.symm ▸ hmem2) hnotin

end CompatMerge


section IsoTest

/-- PlaneGraphIso.thy: `pr_iso_test_rec`.  Isabelle's bounded existentials
`∃F₂ ∈ set Fs₂` / `∃n < length F₂` compile to `List.any`; `remove1` is
`List.erase`.  (The `let I' = zip F₁ (rotate n F₂)` is inlined.) -/
def pr_iso_test_rec [BEq α] [BEq β] : List (α × β) → fgraph α → fgraph β → Bool
  | _, [], Fs₂ => Fs₂.isEmpty
  | I, F₁ :: Fs₁, Fs₂ =>
    Fs₂.any fun F₂ =>
      decide (F₁.length = F₂.length) &&
        (List.range F₂.length).any fun n =>
          compat (F₁.zip (F₂.rotate n)) I &&
            pr_iso_test_rec (merge (F₁.zip (F₂.rotate n)) I) Fs₁ (Fs₂.erase F₂)
termination_by _ Fs₁ _ => Fs₁.length
decreasing_by simp [List.length_cons]

/-- `the ∘ m` (Isabelle), with `default` for `none` (Isabelle: `undefined`). -/
def mapThe [Inhabited β] (m : α → Option β) : α → β := fun x => (m x).getD default

/-- PlaneGraphIso.thy: correctness of the proper-isomorphism search
(`pr_iso_test_rec_corr`).  This collapses Isabelle's refinement chain
`pr_iso_test0_correct` / `test0_conv_test1` / `pr_iso_test2_conv_1` /
`pr_iso_test_rec_conv_2`: the abstract-map stage is `mapOf (zip …)`, the list
stage is `compat`/`merge`, and the rotation bound `n < length F₂` is justified
inline by `List.rotate_mod` (which needs `[] ∉ Fs₂`).  Isabelle's hypothesis
`inj_on m (dom m)` is strengthened to `oneone I`, which is what the
`compat`/`merge` refinement maintains. -/
theorem pr_iso_test_rec_correct [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    [DecidableEq α] [Inhabited β]
    {I : List (α × β)} {Fs₁ : fgraph α} {Fs₂ : fgraph β}
    (hdist1 : ∀ F ∈ Fs₁, F.Nodup) (hdist2 : ∀ F ∈ Fs₂, F.Nodup)
    (hnil : [] ∉ Fs₂)
    (hFs1 : Fs₁.Nodup) (hFs2 : Fs₂.Nodup)
    (hnc1 : noncong Fs₁) (hnc2 : noncong Fs₂)
    (hI : oneone I) :
    pr_iso_test_rec I Fs₁ Fs₂ = true ↔
      ∃ φ, is_pr_iso φ Fs₁ Fs₂ ∧ mapLe (mapOf I) (some ∘ φ) ∧
        Set.InjOn φ (mapDom (mapOf I) ∪ ⋃ F ∈ {F | F ∈ Fs₁}, {v | v ∈ F}) := by
  induction Fs₁ generalizing I Fs₂ with
  | nil =>
    simp only [pr_iso_test_rec, List.isEmpty_iff]
    constructor
    · intro h
      subst h
      refine ⟨mapThe (mapOf I), ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
      · intro F hF
        exact (List.not_mem_nil hF).elim
      · intro F hF
        exact (List.not_mem_nil hF).elim
      · have hU0 : (⋃ F ∈ {F | F ∈ ([] : fgraph α)}, {v | v ∈ F}) = (∅ : Set α) := by
          ext v
          simp
        rw [hU0]
        exact Set.injOn_empty _
      · intro x hx
        cases h : mapOf I x with
        | none => simp [mapDom, h] at hx
        | some y => simp [mapThe, h]
      · have hU0 : (⋃ F ∈ {F | F ∈ ([] : fgraph α)}, {v | v ∈ F}) = (∅ : Set α) := by
          ext v
          simp
        rw [hU0, Set.union_empty]
        intro x hx y hy hxy
        cases hx' : mapOf I x with
        | none => simp [mapDom, hx'] at hx
        | some a =>
          cases hy' : mapOf I y with
          | none => simp [mapDom, hy'] at hy
          | some b =>
            have hab : a = b := by
              have e1 : mapThe (mapOf I) x = a := by simp [mapThe, hx']
              have e2 : mapThe (mapOf I) y = b := by simp [mapThe, hy']
              rw [e1, e2] at hxy
              exact hxy
            exact injOn_mapOf hI.2 hx hy (by rw [hx', hy', hab])
    · rintro ⟨φ, hφ, -, -⟩
      by_contra hne
      obtain ⟨F', hF'⟩ := List.exists_mem_of_ne_nil Fs₂ hne
      obtain ⟨⟨-, hH2⟩, -⟩ := hφ
      obtain ⟨F, hF, -⟩ := hH2 F' hF'
      exact (List.not_mem_nil hF).elim
  | cons F₁ Fs₁ ih =>
    have hdF₁ : F₁.Nodup := hdist1 F₁ List.mem_cons_self
    have hd1t : ∀ F ∈ Fs₁, F.Nodup := fun F hF => hdist1 F (List.mem_cons_of_mem _ hF)
    have hFs1t : Fs₁.Nodup := (List.nodup_cons.mp hFs1).2
    have hnc1t : noncong Fs₁ :=
      fun A hA B hB hc => hnc1 A (List.mem_cons_of_mem _ hA) B (List.mem_cons_of_mem _ hB) hc
    simp only [pr_iso_test_rec, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.mem_range]
    constructor
    · rintro ⟨F₂, hF₂, hlen, n, hn, hcomp, hrec⟩
      have hF₂d : F₂.Nodup := hdist2 F₂ hF₂
      have hlenz : F₁.length = (F₂.rotate n).length :=
        hlen.trans (List.length_rotate F₂ n).symm
      have hI' : oneone (F₁.zip (F₂.rotate n)) := by
        constructor
        · rw [List.map_fst_zip (by omega)]
          exact hdF₁
        · rw [List.map_snd_zip (by omega)]
          exact List.nodup_rotate.mpr hF₂d
      obtain ⟨hle1, -⟩ := (compat_correct hI hI').mp hcomp
      have hmerge_eq : mapOf (merge (F₁.zip (F₂.rotate n)) I) =
          mapAdd (mapOf I) (mapOf (F₁.zip (F₂.rotate n))) := by
        rw [merge_conv_merge0]
        exact merge0_correct hI hI' hcomp
      have hone : oneone (merge (F₁.zip (F₂.rotate n)) I) := by
        rw [merge_conv_merge0]
        exact merge0_inv hI hI' hcomp
      have hd2e : ∀ F ∈ Fs₂.erase F₂, F.Nodup :=
        fun F hF => hdist2 F (List.mem_of_mem_erase hF)
      have hnile : [] ∉ Fs₂.erase F₂ := fun h => hnil (List.mem_of_mem_erase h)
      have hFs2e : (Fs₂.erase F₂).Nodup := hFs2.erase F₂
      have hnc2e : noncong (Fs₂.erase F₂) :=
        fun A hA B hB hc => hnc2 A (List.mem_of_mem_erase hA) B (List.mem_of_mem_erase hB) hc
      obtain ⟨φ, hiso, hle2, hinjφ⟩ :=
        (ih hd1t hd2e hnile hFs1t hFs2e hnc1t hnc2e hone).mp hrec
      have hle2' : mapLe (mapAdd (mapOf I) (mapOf (F₁.zip (F₂.rotate n)))) (some ∘ φ) :=
        hmerge_eq ▸ hle2
      have hleI' : mapLe (mapOf (F₁.zip (F₂.rotate n))) (some ∘ φ) := mapAdd_le_mapE hle2'
      have hleI : mapLe (mapOf I) (some ∘ φ) := mapLe_trans hle1 hle2'
      have hmapF : F₁.map φ = F₂.rotate n := (mapOf_zip_submap hlenz hdF₁).mp hleI'
      have hfst : (F₁.zip (F₂.rotate n)).map Prod.fst = F₁ := List.map_fst_zip (by omega)
      have hdom : mapDom (mapOf (merge (F₁.zip (F₂.rotate n)) I)) =
          mapDom (mapOf I) ∪ {v | v ∈ F₁} := by
        rw [hmerge_eq, mapAdd_dom]
        congr 1
        ext x
        simp only [mapDom, Set.mem_setOf_eq, isSome_mapOf_iff, hfst]
      refine ⟨φ, ?_, hleI, ?_⟩
      · rw [is_iso_Cons hFs1 hFs2 hnc1 hnc2]
        refine ⟨F₂, hF₂, hlen, hiso, ⟨n, hmapF⟩, ?_⟩
        apply Set.InjOn.mono ?_ hinjφ
        intro x hx
        rw [hdom]
        rcases hx with hx | hx
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
      · rw [biUnion_cons_setOf]
        apply Set.InjOn.mono ?_ hinjφ
        intro x hx
        rw [hdom]
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · rcases hx with hx | hx
          · exact Or.inl (Or.inr hx)
          · exact Or.inr hx
    · rintro ⟨φ, hiso, hleI, hinjφ⟩
      rw [is_iso_Cons hFs1 hFs2 hnc1 hnc2] at hiso
      obtain ⟨F₂, hF₂, hlen, hiso', ⟨n, hn⟩, -⟩ := hiso
      have hF₂ne : F₂ ≠ [] := fun he => hnil (he ▸ hF₂)
      have hF₂d : F₂.Nodup := hdist2 F₂ hF₂
      have hn' : n % F₂.length < F₂.length := Nat.mod_lt _ (List.length_pos_iff.mpr hF₂ne)
      have hrotn : F₂.rotate (n % F₂.length) = F₂.rotate n := List.rotate_mod F₂ n
      have hmapF' : F₁.map φ = F₂.rotate (n % F₂.length) := by rw [hrotn]; exact hn
      have hlenz : F₁.length = (F₂.rotate (n % F₂.length)).length :=
        hlen.trans (List.length_rotate F₂ _).symm
      have hI' : oneone (F₁.zip (F₂.rotate (n % F₂.length))) := by
        constructor
        · rw [List.map_fst_zip (by omega)]
          exact hdF₁
        · rw [List.map_snd_zip (by omega)]
          exact List.nodup_rotate.mpr hF₂d
      have hleI' : mapLe (mapOf (F₁.zip (F₂.rotate (n % F₂.length)))) (some ∘ φ) :=
        (mapOf_zip_submap hlenz hdF₁).mpr hmapF'
      have hfst : (F₁.zip (F₂.rotate (n % F₂.length))).map Prod.fst = F₁ :=
        List.map_fst_zip (by omega)
      have hdomI' : mapDom (mapOf (F₁.zip (F₂.rotate (n % F₂.length)))) = {v | v ∈ F₁} := by
        ext x
        simp only [mapDom, Set.mem_setOf_eq, isSome_mapOf_iff, hfst]
      have hcomp : compat (F₁.zip (F₂.rotate (n % F₂.length))) I = true := by
        rw [compat_correct hI hI']
        constructor
        · exact map_compatI hleI hleI'
        · rw [mapAdd_dom, Set.union_comm]
          apply injOn_mapAdd hleI hleI'
          rw [hdomI']
          apply Set.InjOn.mono ?_ hinjφ
          intro x hx
          rcases hx with hx | hx
          · exact Or.inr (Set.mem_biUnion List.mem_cons_self hx)
          · exact Or.inl hx
      have hrec : pr_iso_test_rec (merge (F₁.zip (F₂.rotate (n % F₂.length))) I) Fs₁
          (Fs₂.erase F₂) = true := by
        have hd2e : ∀ F ∈ Fs₂.erase F₂, F.Nodup :=
          fun F hF => hdist2 F (List.mem_of_mem_erase hF)
        have hnile : [] ∉ Fs₂.erase F₂ := fun h => hnil (List.mem_of_mem_erase h)
        have hFs2e : (Fs₂.erase F₂).Nodup := hFs2.erase F₂
        have hnc2e : noncong (Fs₂.erase F₂) :=
          fun A hA B hB hc => hnc2 A (List.mem_of_mem_erase hA) B (List.mem_of_mem_erase hB) hc
        have hmerge_eq : mapOf (merge (F₁.zip (F₂.rotate (n % F₂.length))) I) =
            mapAdd (mapOf I) (mapOf (F₁.zip (F₂.rotate (n % F₂.length)))) := by
          rw [merge_conv_merge0]
          exact merge0_correct hI hI' hcomp
        have hone : oneone (merge (F₁.zip (F₂.rotate (n % F₂.length))) I) := by
          rw [merge_conv_merge0]
          exact merge0_inv hI hI' hcomp
        apply (ih hd1t hd2e hnile hFs1t hFs2e hnc1t hnc2e hone).mpr
        refine ⟨φ, hiso', ?_, ?_⟩
        · rw [hmerge_eq]
          exact mapAdd_le_mapI hleI hleI'
        · rw [hmerge_eq, mapAdd_dom, hdomI']
          apply Set.InjOn.mono ?_ hinjφ
          rw [biUnion_cons_setOf]
          intro x hx
          rcases hx with hx | hx
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inl hx)
          · exact Or.inr (Or.inr hx)
      exact ⟨F₂, hF₂, hlen, n % F₂.length, hn', hcomp, hrec⟩

/-- PlaneGraphIso.thy: `pr_iso_test`. -/
def pr_iso_test [BEq α] [BEq β] (Fs₁ : fgraph α) (Fs₂ : fgraph β) : Bool :=
  pr_iso_test_rec [] Fs₁ Fs₂

/-- PlaneGraphIso.thy: `pr_iso_test_correct`. -/
theorem pr_iso_test_correct [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    [DecidableEq α] [Inhabited β]
    {Fs₁ : fgraph α} {Fs₂ : fgraph β}
    (hdist1 : ∀ F ∈ Fs₁, F.Nodup) (hdist2 : ∀ F ∈ Fs₂, F.Nodup)
    (hnil : [] ∉ Fs₂)
    (hFs1 : Fs₁.Nodup) (hFs2 : Fs₂.Nodup)
    (hnc1 : noncong Fs₁) (hnc2 : noncong Fs₂) :
    pr_iso_test Fs₁ Fs₂ = true ↔ ∃ φ, is_pr_iso φ Fs₁ Fs₂ := by
  unfold pr_iso_test
  rw [pr_iso_test_rec_correct hdist1 hdist2 hnil hFs1 hFs2 hnc1 hnc2 oneone_nil]
  constructor
  · rintro ⟨φ, hφ, -, -⟩
    exact ⟨φ, hφ⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, hφ, ?_, ?_⟩
    · intro x hx
      simp [mapDom] at hx
    · have hdom0 : mapDom (mapOf ([] : List (α × β))) = (∅ : Set α) := by
        ext x
        simp [mapDom]
      rw [hdom0, Set.empty_union]
      exact hφ.2

/-- `set (map rev g₂) = rev '' set g₂`. -/
theorem set_map_reverse (Fs : fgraph α) :
    {F | F ∈ Fs.map List.reverse} = List.reverse '' {F | F ∈ Fs} := by
  ext F
  constructor
  · intro h
    obtain ⟨F₀, hF₀, rfl⟩ := List.mem_map.mp h
    exact ⟨F₀, hF₀, rfl⟩
  · rintro ⟨F₀, hF₀, rfl⟩
    exact List.mem_map_of_mem hF₀

/-- PlaneGraphIso.thy: `iso_test`
(`pr_iso_test g₁ g₂ ∨ pr_iso_test g₁ (map rev g₂)`). -/
def iso_test [BEq α] [BEq β] (g₁ : fgraph α) (g₂ : fgraph β) : Bool :=
  pr_iso_test g₁ g₂ || pr_iso_test g₁ (g₂.map List.reverse)

/-- PlaneGraphIso.thy: `iso_correct`. -/
theorem iso_correct [BEq α] [LawfulBEq α] [DecidableEq α] [Inhabited α]
    {Fs₁ Fs₂ : fgraph α}
    (hdist1 : ∀ F ∈ Fs₁, F.Nodup) (hdist2 : ∀ F ∈ Fs₂, F.Nodup)
    (hnil : [] ∉ Fs₂)
    (hFs1 : Fs₁.Nodup) (hFs2 : Fs₂.Nodup)
    (hnc1 : noncong Fs₁) (hnc2 : noncong Fs₂) :
    iso_test Fs₁ Fs₂ = true ↔ Fs₁ ≃ Fs₂ := by
  have hdist2' : ∀ F ∈ Fs₂.map List.reverse, F.Nodup := by
    intro F hF
    obtain ⟨F₀, hF₀, rfl⟩ := List.mem_map.mp hF
    exact List.nodup_reverse.mpr (hdist2 F₀ hF₀)
  have hnil' : [] ∉ Fs₂.map List.reverse := by
    intro h
    obtain ⟨F₀, hF₀, he⟩ := List.mem_map.mp h
    exact hnil (List.reverse_eq_nil_iff.mp he ▸ hF₀)
  have hFs2' : (Fs₂.map List.reverse).Nodup := hFs2.map List.reverse_injective
  have hnc2' : noncong (Fs₂.map List.reverse) := by
    intro A hA B hB hc
    obtain ⟨A₀, hA₀, rfl⟩ := List.mem_map.mp hA
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    have h := hnc2 A₀ hA₀ B₀ hB₀ (list_cong_rev_iff.mp hc)
    rw [h]
  unfold iso_test
  rw [Bool.or_eq_true, pr_iso_test_correct hdist1 hdist2 hnil hFs1 hFs2 hnc1 hnc2,
    pr_iso_test_correct hdist1 hdist2' hnil' hFs1 hFs2' hnc1 hnc2']
  constructor
  · rintro (⟨φ, hφ⟩ | ⟨φ, hφ⟩)
    · exact ⟨φ, Or.inl hφ⟩
    · refine ⟨φ, Or.inr ?_⟩
      show is_pr_Iso φ {F | F ∈ Fs₁} (List.reverse '' {F | F ∈ Fs₂})
      rw [← set_map_reverse]
      exact hφ
  · rintro ⟨φ, hφ⟩
    unfold is_iso is_Iso at hφ
    rcases hφ with hφ | hφ
    · exact Or.inl ⟨φ, hφ⟩
    · refine Or.inr ⟨φ, ?_⟩
      show is_pr_Iso φ {F | F ∈ Fs₁} {F | F ∈ Fs₂.map List.reverse}
      rw [set_map_reverse]
      exact hφ

end IsoTest

end Kepler.Graphs
