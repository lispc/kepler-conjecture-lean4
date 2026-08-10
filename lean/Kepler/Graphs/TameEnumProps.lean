/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `TameEnumProps.thy`.

Source: `reference/afp-flyspeck-tame/TameEnumProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

`TameEnumProps.thy` imports `GeneratorProps`; the two lemmas are the
completeness of the final-graph filter (`untame_negFin`: reachable final
tame graphs pass the executable `is_tame` test) and `next_tame_comp`
(lifting reachability from `next_tame0` to `next_tame`).

`filter_tame_succs'` is the `Prop`-predicate variant of
`TameProps.filter_tame_succs` (the `inv` invariant is a `Prop` here), cf. the
`filterout_untame_succs'` precedent in `GeneratorProps.lean`.
-/
import Kepler.Graphs.GeneratorProps

namespace Kepler.Graphs

/-- `TameEnumProps.thy: untame_negFin`. -/
theorem untame_negFin {g : Graph} (pl : inv g) (fin : g.final = true) (ht : tame g) :
    is_tame g = true := by
  have ht' := ht
  obtain ⟨-, h10, h11a, -, h12o, w, adm, hsum⟩ := ht'
  have hw : (∑ₗ f ∈ g.faces, w f) < squanderTarget := by
    rwa [ListSum_eq_sum_map]
  have hlb := total_weight_lowerbound pl fin ht adm hw
  have h13 : is_tame13a g = true := by
    rw [is_tame13a, decide_eq_true_eq]
    omega
  simp [is_tame, h10, h11a, h12o, h13]

/-- `Prop`-predicate variant of `TameProps.filter_tame_succs`. -/
theorem filter_tame_succs' {P : Graph → Prop} {ok : Graph → Bool}
    {succs : Graph → List Graph}
    (invP : ∀ g g', g' ∈ succs g → P g → P g')
    (fin : ∀ g, g.final = true → succs g = [])
    (ok_untame : ∀ g, P g → !ok g = true → g.final = true ∧ ¬ tame g)
    {g g' : Graph} (gg' : RTranCl succs g g') :
    P g → g'.final = true → tame g' → RTranCl (fun g => (succs g).filter ok) g g' := by
  induction gg' with
  | refl => exact fun _ _ _ => .refl
  | succs hh' h'h'' ih =>
    rename_i h h' h''
    intro hP hfin htame
    have hP' : P h' := invP _ _ hh' hP
    cases hok : ok h' with
    | true =>
      exact .succs (List.mem_filter.mpr ⟨hh', hok⟩) (ih hP' hfin htame)
    | false =>
      obtain ⟨hf', ht'⟩ := ok_untame h' hP' (by simp [hok])
      have heq : h'' = h' := by
        cases h'h'' with
        | refl => rfl
        | succs hm _ => exact absurd (fin h' hf' ▸ hm) List.not_mem_nil
      exact absurd (heq ▸ htame) ht'

/-- `TameEnumProps.thy: next_tame_comp`. -/
theorem next_tame_comp {p : Nat} {g : Graph}
    (ht : tame g) (hfin : g.final = true)
    (hr : RTranCl (next_tame0 p) (Seed p) g) :
    RTranCl (next_tame p) (Seed p) g := by
  have fin0 : ∀ g, g.final = true → next_tame0 p g = [] := by
    intro g hg
    have h : (nonFinals g).isEmpty = true := hg
    simp [next_tame0, h]
  have oku : ∀ g, inv g → !(fun g' => !g'.final || is_tame g') g = true →
      g.final = true ∧ ¬ tame g := by
    intro g hinv hok
    cases hf : g.final with
    | true =>
      refine ⟨rfl, fun ht => ?_⟩
      have hi : is_tame g = true := untame_negFin hinv hf ht
      simp [hf, hi] at hok
    | false =>
      simp [hf] at hok
  exact filter_tame_succs' inv_inv_next_tame0 fin0 oku hr inv_Seed hfin ht

end Kepler.Graphs
