\ hello-world LP for SoPlex exact-rational smoke test
\ max x + y  s.t. 2x + y <= 4, x + 2y <= 5, x,y >= 0 (LP format default bounds)
\ exact optimum: x = 1, y = 2, objective = 3
Maximize
 obj: x + y
Subject To
 c1: 2 x + y <= 4
 c2: x + 2 y <= 5
End
