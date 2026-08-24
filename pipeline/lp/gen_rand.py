#!/usr/bin/env python3
"""gen_rand.py — generate a random bounded, feasible LP with integral data.

Usage: gen_rand.py ROWS COLS SEED > file.lp

Guarantees (by construction): variables x ≥ 0 (LP-format default), only `<=`
rows, A ≥ 0 with at least one positive entry per column (hence bounded:
x_j ≤ b_i / A_ij), and a known feasible point (b = A·x* + slack, x*,slack ≥ 0).
Coefficients are integers, so the file is accepted by `socert.py`.
"""

import random
import sys


def main() -> None:
    m, n, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    # ~60% sparse nonnegative matrix
    A = [[rng.choice([0, 0, 1, 2, 3, 4, 5]) for _ in range(n)] for _ in range(m)]
    for j in range(n):
        if all(A[i][j] == 0 for i in range(m)):
            A[rng.randrange(m)][j] = rng.randint(1, 5)
    x_star = [rng.randint(0, 2) for _ in range(n)]
    slack = [rng.randint(0, 5) for _ in range(m)]
    b = [sum(A[i][j] * x_star[j] for j in range(n)) + slack[i] for i in range(m)]
    c = [rng.randint(1, 9) for _ in range(n)]

    print(f"\\ random bounded LP: {m} rows, {n} cols, seed {seed} (gen_rand.py)")
    print("Maximize")
    print(" obj: " + " + ".join(f"{c[j]} v{j}" for j in range(n)))
    print("Subject To")
    for i in range(m):
        terms = [f"{A[i][j]} v{j}" for j in range(n) if A[i][j] != 0]
        lhs = " + ".join(terms) if terms else "0 v0"
        print(f" r{i}: {lhs} <= {b[i]}")
    print("End")


if __name__ == "__main__":
    main()
