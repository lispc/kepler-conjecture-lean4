/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Quasi_Order.thy`.

Source: `reference/afp-flyspeck-tame/Quasi_Order.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Isabelle's `locale quasi_order` fixes a relation `qle` with reflexivity and
transitivity; here it becomes the structure `QuasiOrder qle`.  The relations
`in_qle` (`∈≼`), `subseteq_qle` (`⊆≼`) and `seteq_qle` (`=≼`) take `qle` as an
explicit first argument; the notations are scoped to `Kepler.Graphs` and index
the relation implicitly through a `QuasiOrder` hypothesis is not possible, so
they are only provided at the `iso_fgraph` instance in `PlaneGraphIso.lean`
(`∈ₛ`, `⊆ₛ`, `=ₛ`), exactly as Isabelle does via `qle_gr` abbreviations.
-/
import Mathlib.Data.Set.Defs

namespace Kepler.Graphs

variable {α : Type _}

/-- Quasi_Order.thy: locale `quasi_order`. A reflexive, transitive relation. -/
structure QuasiOrder (qle : α → α → Prop) : Prop where
  /-- `qle_refl` -/
  qle_refl : ∀ x, qle x x
  /-- `qle_trans` -/
  qle_trans : ∀ x y z, qle x y → qle y z → qle x z

/-- Quasi_Order.thy: `in_qle` (`x ∈≼ M ≡ ∃y ∈ M. x ≼ y`). -/
def inQle (qle : α → α → Prop) (x : α) (M : Set α) : Prop :=
  ∃ y ∈ M, qle x y

/-- Quasi_Order.thy: `subseteq_qle` (`M ⊆≼ N ≡ ∀x ∈ M. x ∈≼ N`). -/
def subseteqQle (qle : α → α → Prop) (M N : Set α) : Prop :=
  ∀ x ∈ M, inQle qle x N

/-- Quasi_Order.thy: `seteq_qle` (`M =≼ N ≡ M ⊆≼ N ∧ N ⊆≼ M`). -/
def seteqQle (qle : α → α → Prop) (M N : Set α) : Prop :=
  subseteqQle qle M N ∧ subseteqQle qle N M

/-- Quasi_Order.thy: `subseteq_qle_refl` -/
theorem subseteqQle_refl (hq : QuasiOrder qle) (M : Set α) : subseteqQle qle M M :=
  fun x hx => ⟨x, hx, hq.qle_refl x⟩

/-- Quasi_Order.thy: `subseteq_qle_trans` -/
theorem subseteqQle_trans (hq : QuasiOrder qle) {A B C : Set α} (hAB : subseteqQle qle A B)
    (hBC : subseteqQle qle B C) : subseteqQle qle A C := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hAB x hx
  obtain ⟨z, hz, hyz⟩ := hBC y hy
  exact ⟨z, hz, hq.qle_trans x y z hxy hyz⟩

/-- Quasi_Order.thy: `empty_subseteq_qle` -/
theorem empty_subseteqQle (A : Set α) : subseteqQle qle ∅ A :=
  fun _ hx => hx.elim

variable {qle : α → α → Prop}

/-- Quasi_Order.thy: `subseteq_qleI2` -/
theorem subseteqQleI2 {M N : Set α} (h : ∀ x ∈ M, ∃ y ∈ N, qle x y) :
    subseteqQle qle M N :=
  h

/-- Quasi_Order.thy: `subseteq_qleD2` -/
theorem subseteqQleD2 {M N : Set α} (h : subseteqQle qle M N) {x : α} (hx : x ∈ M) :
    ∃ y ∈ N, qle x y :=
  h x hx

/-- Quasi_Order.thy: `seteq_qle_refl` -/
theorem seteqQle_refl (hq : QuasiOrder qle) (A : Set α) : seteqQle qle A A :=
  ⟨subseteqQle_refl hq A, subseteqQle_refl hq A⟩

/-- Quasi_Order.thy: `seteq_qle_trans` -/
theorem seteqQle_trans (hq : QuasiOrder qle) {A B C : Set α} (hAB : seteqQle qle A B)
    (hBC : seteqQle qle B C) : seteqQle qle A C :=
  ⟨subseteqQle_trans hq hAB.1 hBC.1, subseteqQle_trans hq hBC.2 hAB.2⟩

end Kepler.Graphs
