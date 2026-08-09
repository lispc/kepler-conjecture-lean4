import Kepler.LP.HelloChecker

-- Axiom audit for G0's hello-checker: must print only the standard axioms
-- (or none). Any `sorryAx` or project-introduced axiom fails the audit.
#print axioms Kepler.LP.example_bound
