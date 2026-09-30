"""Smallest value of Q_{F_C}(h)/||h||_2^2 over step functions h on n cells of [-1,1] with int h = 0.
Positive => the discretised shape-(d) functional is strictly convex on {int f = 1} (numerical, float)."""
import numpy as np, sys
from certify import G2_float
def mineig(C, n):
    h = 2.0 / n
    d = (np.arange(n)[:, None] - np.arange(n)[None, :]) * h
    M = h * np.eye(n) + (G2_float(d + h, C) - 2 * G2_float(d, C) + G2_float(d - h, C))
    # basis of {sum x = 0}
    B = np.linalg.qr(np.eye(n) - np.ones((n, n)) / n)[0][:, :n-1]
    A = B.T @ M @ B / h          # ||h||^2 = h sum x_i^2
    return np.linalg.eigvalsh(0.5 * (A + A.T))[0]
for C in [1.0, 1.0434, 1.0911, 1.2688, 1.3448, 1.603, 1.8]:
    print(f"C={C}: min Q(h)/||h||^2 on int h=0: n=400 {mineig(C,400):.4f}  n=800 {mineig(C,800):.4f}", flush=True)
