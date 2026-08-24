import Kepler.Statement
import Kepler.LP.HelloChecker
import Kepler.Graphs.TameClassification

-- Axiom audit: must print only the standard axioms (or none).
-- Any `sorryAx` (except on the explicitly allowed Phase-1 placeholder
-- `the_kepler_conjecture`) or project-introduced axiom fails the audit.
#print axioms Kepler.LP.example_bound
#print axioms Kepler.Packing.finite_inter_ball
-- Phase 1: the proof body of the main statement is a sanctioned `sorry`
-- (PLAN.md §4 Phase 1); this line documents that fact in CI output.
#print axioms Kepler.the_kepler_conjecture
-- G2: standard axioms + the scoped native_decide trust axioms
-- (DECISIONS.md 2026-08-10; per-seed counts recorded in
-- docs/architecture.md "建成状态"); no sorryAx allowed here.
#print axioms Kepler.Graphs.tame_classification
