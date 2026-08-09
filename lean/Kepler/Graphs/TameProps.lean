/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `TameProps.thy`.

Source: `reference/afp-flyspeck-tame/TameProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

`TameProps.thy` imports `RTranCl`; the two `RTranCl.thy` helpers it needs
(`invariant`, `RTranCl_inv`) are ported here as well. Like
`Kepler.Graphs.RTranCl` (Plane.lean), they are specialized to `Graph` —
Isabelle's `RTranCl` is polymorphic, but `TameProps` uses it only at type
`graph`. Isabelle `bool` predicates are ported as `Graph → Bool` (coerced
to `Prop` in hypotheses), matching the style of `Tame.lean`.
-/
import Kepler.Graphs.Tame

namespace Kepler.Graphs

/-- `RTranCl.thy: invariant` (specialized to `Graph`). -/
def invariant (P : Graph → Bool) (succs : Graph → List Graph) : Prop :=
  ∀ g g', g' ∈ succs g → P g → P g'

/-- `RTranCl.thy: RTranCl_inv`. -/
theorem RTranCl_inv {P : Graph → Bool} {succs : Graph → List Graph}
    (hinv : invariant P succs) {g g' : Graph} (hg : RTranCl succs g g') :
    P g → P g' := by
  induction hg with
  | refl => exact id
  | succs hh' _ ih => exact fun h => ih (hinv _ _ hh' h)

/-- `TameProps.thy: length_disj_filter_le`. -/
theorem length_disj_filter_le {α : Type*} {P Q : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, !(P x && Q x)) :
    (xs.filter P).length + (xs.filter Q).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : !(P x && Q x) := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    cases hP : P x <;> cases hQ : Q x <;>
      simp_all [List.length_cons] <;> omega

/-- `TameProps.thy: tri_quad_le_degree`. -/
theorem tri_quad_le_degree (g : Graph) (v : Vertex) :
    tri g v + quad g v ≤ degree g v := by
  have hdisj : ∀ f ∈ g.facesAt v,
      !((f.final && f.vertices.length == 3) && (f.final && f.vertices.length == 4)) := by
    intro f _
    cases h3 : (f.vertices.length == 3) <;> cases h4 : (f.vertices.length == 4) <;>
      simp_all
  exact length_disj_filter_le hdisj

/-- `TameProps.thy: faceCountMax_bound`. -/
theorem faceCountMax_bound {g : Graph} {v : Vertex} (hg : tame g) (hv : v ∈ g.vertices) :
    tri g v + quad g v ≤ 7 := by
  obtain ⟨-, -, -, h11b, -, -⟩ := hg
  have hdeg : degree g v ≤ 7 := by
    have h : decide (degree g v ≤ if except g v = 0 then 7 else 6) = true :=
      List.all_eq_true.mp h11b v hv
    rw [decide_eq_true_eq] at h
    split at h <;> omega
  have h2 := tri_quad_le_degree g v
  omega

/-- `TameProps.thy: filter_tame_succs`. -/
theorem filter_tame_succs {P ok : Graph → Bool} {succs : Graph → List Graph}
    (invP : invariant P succs)
    (fin : ∀ g, g.final → succs g = [])
    (ok_untame : ∀ g, P g → !ok g → g.final ∧ ¬ tame g)
    {g g' : Graph} (gg' : RTranCl succs g g') :
    P g → g'.final → tame g' → RTranCl (fun g => (succs g).filter ok) g g' := by
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

/-- `TameProps.thy: untame`. -/
def untame (P : Graph → Bool) : Prop :=
  ∀ g, g.final → P g → ¬ tame g

/-- `TameProps.thy: filterout_untame_succs`. -/
theorem filterout_untame_succs {P U : Graph → Bool} {f f' : Graph → List Graph}
    (invP : invariant P f)
    (invPU : invariant (fun g => P g && U g) f)
    (huntame : untame (fun g => P g && U g))
    (new_untame : ∀ g g', P g → g' ∈ f g → g' ∉ f' g → U g')
    {g g' : Graph} (gg' : RTranCl f g g') :
    P g → g'.final → tame g' → RTranCl f' g g' := by
  induction gg' with
  | refl => exact fun _ _ _ => .refl
  | succs hh' h'h'' ih =>
    rename_i h h' h''
    intro hP hfin htame
    have hP' : P h' := invP _ _ hh' hP
    by_cases hm : h' ∈ f' h
    · exact .succs hm (ih hP' hfin htame)
    · have hU' : U h' := new_untame h h' hP hh' hm
      have hPU' : P h' && U h' := by simp [hP', hU']
      have hPU'' := RTranCl_inv invPU h'h'' hPU'
      exact absurd htame (huntame h'' hfin hPU'')

end Kepler.Graphs
