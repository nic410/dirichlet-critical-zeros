"""Exact rational certificates for the two cases of Section 8.2 of the paper ("Which ingredient gives what"):
item (a), shape e (F = C min(a, 1)) with C = 12688/10000, and item (b), shape d (F = F_C) with C = 4175/1000 >= 2/E.
The log labels them "Tier1 (e)" and "Tier0 (d)". The certificates are symmetrised so that the window is even."""
import math
import numpy as np
from fractions import Fraction as Fr
from extremal import solve
def exactJ(f, shape, C):
    n = len(f); h = Fr(2, n)
    f = 0.5 * (np.maximum(f, 0.0) + np.maximum(f, 0.0)[::-1])  # symmetrise: even window
    fr = [Fr(float(v)) for v in f]; fr = [(a + b) / 2 for a, b in zip(fr, fr[::-1])]; s = sum(fr) * h; fr = [v / s for v in fr]
    def G2(xx):
        xx = abs(xx)
        if shape == 'e':
            return C * xx**3 / 6 if xx <= 1 else C / 6 + C * (xx - 1) / 2 + C * (xx - 1)**2 / 2
        return xx**3 / 6 if xx <= 1 else Fr(1, 6) + (xx - 1) / 2 + C * (xx - 1)**2 / 2
    J = h * sum(v * v for v in fr)
    for dd in range(-(n - 1), n):
        d = dd * h; K = G2(d + h) - 2 * G2(d) + G2(d - h)
        J += K * sum(fr[i] * fr[i - dd] for i in range(max(0, dd), min(n, n + dd)))
    return J
for name, shape, Cf, Cr in [("Tier1 (e)", 'e', 1.2688, Fr(12688, 10000)), ("Tier0 (d)", 'd', 4.175, Fr(4175, 1000))]:
    J0, f, x = solve(2.0, shape, Cf, n=300, starts=4)
    J = exactJ(f, shape, Cr)
    # certified values printed as true floors of the exact rationals
    pf = Fr(math.floor((2 - J) * 10**6), 10**6); df = Fr(math.floor((3 - J) / 2 * 10**6), 10**6)
    print(f"{name}: float p={2-J0:.6f}; certified p >= {float(pf):.6f}, distinct >= {float(df):.6f}", flush=True)
