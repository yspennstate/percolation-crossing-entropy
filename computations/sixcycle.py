# -*- coding: utf-8 -*-
"""Recompute the six-cycle Gram matrix of the section "A six-cycle coercivity inequality" from the definitions,
check the numbers stated there, and write an exact LDL^T certificate for the odd block to sixcycle.json."""
from fractions import Fraction as Fr
import itertools
import json
import math
import sys

import numpy as np

N = 6
bit = lambda m, i: (m >> i) & 1
sgn = lambda z, i: 1 if bit(z, i) else -1          # bit 1 = plus sign
changes = lambda z: sum(bit(z, i) != bit(z, (i + 1) % N) for i in range(N))
L = [z for z in range(64) if changes(z) <= 2]
H = [z for z in range(64) if changes(z) > 2]
indep = [A for A in range(64) if all(not (bit(A, i) and bit(A, (i + 1) % N)) for i in range(N))]
mask = lambda *s: sum(1 << i for i in s)
EVEN = [0] + [mask(i, (i + 2) % 6) for i in range(6)] + [mask(i, i + 3) for i in range(3)]
ODD = [mask(i) for i in range(6)] + [mask(0, 2, 4), mask(1, 3, 5)]
ORDER = EVEN + ODD
chi = lambda A, z: math.prod(sgn(z, i) for i in range(N) if bit(A, i))
assert len(L) == 32 and len(H) == 32 and len(indep) == 18 and sorted(ORDER) == sorted(indep) and len(set(ORDER)) == 18
# L = empty, full, or one cyclic interval of plus signs
ivals = {0, 63} | {sum(1 << ((s + k) % 6) for k in range(l)) for s in range(6) for l in range(1, 6)}
assert set(L) == ivals, "L is not the set of interval configurations"
G = np.array([[sum(chi(A, z) * chi(B, z) for z in L) for B in ORDER] for A in ORDER])
Gall = np.array([[sum(chi(A, z) * chi(B, z) for z in range(64)) for B in ORDER] for A in ORDER])
assert (Gall == 64 * np.eye(18, dtype=int)).all(), "characters not orthogonal"
# parity: no even-odd coupling
assert (G[:10, 10:] == 0).all()
Ge = G[:10, :10]
assert (Ge[:7, :7] == 32 * np.eye(7, dtype=int)).all() and (Ge[7:, 7:] == 32 * np.eye(3, dtype=int)).all()
K = Ge[:7, 7:]
print("K rows:", K.tolist())
assert (K.T @ K == 512 * np.eye(3, dtype=int) + 112 * np.ones((3, 3), dtype=int)).all()
Go = G[10:, 10:]
print("singleton block first row:", Go[0, :6].tolist(), " triple block:", Go[6:, 6:].tolist())
print("singleton-triple couplings:", Go[:6, 6:].tolist())
ev = sorted(np.linalg.eigvalsh(G.astype(float)))
claimed = sorted([32 + 4 * math.sqrt(53), 32 - 4 * math.sqrt(53)] + [32 + 16 * math.sqrt(2)] * 2 +
                 [32 - 16 * math.sqrt(2)] * 2 + [32] * 4 + [40 + 8 * math.sqrt(3), 40 - 8 * math.sqrt(3),
                 24 + 8 * math.sqrt(3), 24 - 8 * math.sqrt(3)] + [48] * 2 + [16] * 2)
print("max |eig - claimed| =", max(abs(a - b) for a, b in zip(ev, claimed)))
print("least eigenvalue", ev[0], "vs 32-4sqrt53 =", 32 - 4 * math.sqrt(53), " a* =", ev[0] / 64, (8 - math.sqrt(53)) / 16)


# exact LDL^T of (Go - c I) for the odd block, c = 3
def ldl(M):
    n = len(M)
    A = [[Fr(int(x)) for x in row] for row in M]
    Lm = [[Fr(0)] * n for _ in range(n)]
    D = [Fr(0)] * n
    for j in range(n):
        D[j] = A[j][j] - sum(Lm[j][k] ** 2 * D[k] for k in range(j))
        Lm[j][j] = Fr(1)
        for i in range(j + 1, n):
            Lm[i][j] = (A[i][j] - sum(Lm[i][k] * Lm[j][k] * D[k] for k in range(j))) / D[j]
    return Lm, D


c = 3
Lm, D = ldl(Go - c * np.eye(8, dtype=int))
print("odd block LDL pivots (c=3):", [str(d) for d in D])
assert all(d > 0 for d in D)
json.dump({"ORDER": ORDER, "L": L, "G": G.tolist(), "K": K.tolist(), "Go": Go.tolist(),
           "ldl_L": [[str(x) for x in r] for r in Lm], "ldl_D": [str(d) for d in D]},
          open(sys.argv[1] if len(sys.argv) > 1 else "sixcycle.json", "w"))
# sharpness vector: b = (1,1,1), a = -K b / sqrt(848)
s = math.sqrt(848)
b = np.ones(3)
a = -K @ b / s
u = np.concatenate([a, b, np.zeros(8)])
print("Rayleigh quotient at the sharp vector:", u @ G @ u / (u @ u), " K b =", (K @ b).tolist())
