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
    mapLe m₁ m₃ := fun x hx => (h₁ x hx).trans (h₂ x (h₁ x hx ▸ hx))

/-- Isabelle's `map_add_le_mapE`. -/
theorem mapAdd_le_mapE {m m' h : α → Option β} (hl : mapLe (mapAdd m m') h) : mapLe m' h := by
  intro x hx
  cases hx' : m' x with
  | none => simp [mapDom, hx'] at hx
  | some v =>
    have e := hl x (by rw [mapDom, Set.mem_setOf_eq, mapAdd_eq_right hx']; rfl)
    rwa [mapAdd_eq_right hx'] at e

/-- Isabelle's `map_add_le_mapI`. -/
theorem mapAdd_le_mapI {m m' h : α → Option β} (hl : mapLe m h) (hr : mapLe m' h) :
    mapLe (mapAdd m m') h := by
  intro x hx
  cases hx' : m' x with
  | some v =>
    rw [mapAdd_eq_right hx']
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

/-- Isabelle's `[simp]` lemma `distinct(map snd xys) ⟹ inj_on (map_of xys)
(dom (map_of xys))`. -/
theorem injOn_mapOf [DecidableEq α] {ps : List (α × β)}
    (hd : (ps.map Prod.snd).Nodup) : Set.InjOn (mapOf ps) (mapDom (mapOf ps)) := by
  induction ps with
  | nil => intro x hx; simp [mapDom] at hx
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    have hd' : (ps.map Prod.snd).Nodup := (List.nodup_cons.mp hd).2
    have hb : b ∉ ps.map Prod.snd := (List.nodup_cons.mp hd).1
    intro x hx y hy hxy
    by_cases hxa : x = a
    · by_cases hya : y = a
      · exact hxa.trans hya.symm
      · subst hxa
        rw [mapOf_cons, if_pos rfl, mapOf_cons, if_neg hya] at hxy
        -- hxy : some b = mapOf ps y
        have hmem : (y, b) ∈ ps := mem_of_mapOf_eq_some hxy.symm
        exact absurd (List.mem_map_of_mem hmem) hb
    · by_cases hya : y = a
      · subst hya
        rw [mapOf_cons, if_pos rfl, mapOf_cons, if_neg hxa] at hxy
        have hmem : (x, b) ∈ ps := mem_of_mapOf_eq_some hxy
        exact absurd (List.mem_map_of_mem hmem) hb
      · rw [mapOf_cons, if_neg hxa, mapOf_cons, if_neg hya] at hxy
        apply ih hd'
        · rw [mapDom, Set.mem_setOf_eq] at hx ⊢
          rw [mapOf_cons, if_neg hxa] at hx
          exact hx
        · rw [mapDom, Set.mem_setOf_eq] at hy ⊢
          rw [mapOf_cons, if_neg hya] at hy
          exact hy
        · exact hxy

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
      rw [List.zip_cons_cons, List.map_cons, List.cons.injEq, ih hlen hd']
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
            rwa [List.map_fst_zip (by have h2 := List.length_zip (l₁ := xs) (l₂ := ys); omega)] at hm
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
          rw [mapOf_cons, if_pos rfl]
          -- goal: some y = (some ∘ f) x
          rw [← h1]
        · rw [mapOf_cons, if_neg hzx]
          apply h2
          rw [mapDom, Set.mem_setOf_eq] at hz ⊢
          rw [mapOf_cons, if_neg hzx] at hz
          exact hz

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

end Kepler.Graphs
