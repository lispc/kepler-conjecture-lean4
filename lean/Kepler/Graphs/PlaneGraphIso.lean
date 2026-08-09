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
- The bounded existentials `∃F₂ ∈ set Fs₂` / `∃n < length F₂` in the
  executable tests are compiled to `List.any` over `Fs₂` resp.
  `List.range F₂.length`; `compat`/`merge` use `==` (`BEq`) for the
  executable equality tests Isabelle writes with `=`.
-/
import Kepler.Graphs.RotationLemmas
import Kepler.Graphs.QuasiOrder
import Mathlib.Data.List.Rotate
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
  have hU : (⋃ F ∈ {F | F ∈ F₁ :: Fs₁'}, {v | v ∈ F}) =
      {v | v ∈ F₁} ∪ ⋃ F ∈ {F | F ∈ Fs₁'}, {v | v ∈ F} := by
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
    · rw [← hU]; exact hinj
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
    · rw [hU]; exact hinj

end IsoCons

end Kepler.Graphs
