; dReal smoke test: 证明 forall x in [1.5, 2], x^2 - 2 > 0
; 取否定: exists x in [1.5, 2], x^2 - 2 <= 0, 应为 unsat (delta = 1e-3)
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (<= 1.5 x))
(assert (<= x 2.0))
(assert (<= (- (* x x) 2) 0))
(check-sat)
(exit)
