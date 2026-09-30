"""Exact rational certificates for p(C) = 2 - inf Q_{F_C}(f), shape (d): F_C(a) = a on [0,1], C on (1,2].

For each rational C we
  1. solve the discretised problem (f piecewise constant on n equal cells of [-1,1]) in floating point
     via the KKT system  M f = mu c  (the shape-(d) form is convex on {int f = 1} for C <~ 1.6;
     positivity of the solution is checked, so the constraint f >= 0 is inactive);
  2. symmetrise, round the step heights to integers m_i (scale 1e9), and renormalise EXACTLY so that
     int f = 1;
  3. evaluate Q_{F_C}(f) for that explicit step function in exact rational arithmetic, using the exact
     cell-pair integrals  int_{cell i} int_{cell j} F(|u-v|) = G2(d+h) - 2 G2(d) + G2(d-h),
     G2'' = F(|.|), G2(0) = G2'(0) = 0.
Any admissible f gives p(C) >= 2 - Q(f) and distinct >= (3 - Q(f))/2, so the printed bounds are
rigorous lower bounds for the variational constants (no claim of optimality is needed).
Run:  taskset -c 0-3 python3 certify_ctplus.py C1 C2 ... (rationals as strings)  (a copy of certify.py)
"""
import math
import sys
import numpy as np
from fractions import Fraction as Fr


def G2_float(x, C):
    x = np.abs(x)
    return np.where(x <= 1, x**3 / 6, 1 / 6 + (x - 1) / 2 + C * (x - 1)**2 / 2)


def G2_exact(x, C):
    x = abs(x)
    if x <= 1:
        return x**3 / 6
    return Fr(1, 6) + (x - 1) / 2 + C * (x - 1)**2 / 2


def solve_float(C, n):
    h = 2.0 / n
    d = (np.arange(n)[:, None] - np.arange(n)[None, :]) * h
    M = h * np.eye(n) + (G2_float(d + h, C) - 2 * G2_float(d, C) + G2_float(d - h, C))
    c = h * np.ones(n)
    f = np.linalg.solve(M, c)
    f /= c @ f
    return f, float(f @ M @ f)


def exact_Q(m, C, n):
    """m: list of nonnegative ints (step heights up to a common factor); returns exact Q(f), f normalised."""
    h = Fr(2, n)
    S = sum(m)
    # f_i = m_i / (h S)
    Kd = {}
    for dd in range(-(n - 1), n):
        d = dd * h
        Kd[dd] = G2_exact(d + h, C) - 2 * G2_exact(d, C) + G2_exact(d - h, C)
    # sum_i f_i^2 * h  +  sum_dd K[dd] * sum_i f_i f_{i-dd}
    diag = sum(x * x for x in m)
    tot = h * diag
    for dd in range(-(n - 1), n):
        corr = sum(m[i] * m[i - dd] for i in range(max(0, dd), min(n, n + dd)))
        tot += Kd[dd] * corr
    return tot / (h * S) ** 2


def certify(Cstr, n=400, scale=10**9):
    C = Fr(Cstr)
    f, Qf = solve_float(float(C), n)
    fmin = f.min()
    if fmin <= 0:
        print(f"C={Cstr}: float solution not positive (min {fmin:.3e}); skipping", flush=True)
        return None
    fs = 0.5 * (f + f[::-1])
    m = [int(round(v * scale)) for v in fs]
    m = [(a + b) // 2 for a, b in zip(m, m[::-1])]  # exact symmetry
    Q = exact_Q(m, C, n)
    p = 2 - Q
    dist = (3 - Q) / 2
    # floor to 6 decimals for reporting (rigorous: floor of an exact rational)
    pf = Fr(int(p * 10**6), 10**6)
    df = Fr(int(dist * 10**6), 10**6)
    # 9-digit values printed as true floors of the exact rationals (math.floor of a Fraction is exact), so that
    # "EXACT p >= x" is a valid inequality (as in certify_hybrid.py).
    p9 = Fr(math.floor(p * 10**9), 10**9)
    d9 = Fr(math.floor(dist * 10**9), 10**9)
    print(f"C={Cstr} (={float(C):.6f}) n={n}: float p={2-Qf:.7f}; EXACT p >= {float(p9):.9f} "
          f"(certified >= {float(pf):.6f}); distinct >= {float(d9):.9f} (certified >= {float(df):.6f}); "
          f"min f = {fmin:.4f}", flush=True)
    return p, dist


if __name__ == '__main__':
    # usage: python3 certify_ctplus.py n C1 C2 ...   (each C a decimal/rational string, rounded UP from the certified bound)
    n = int(sys.argv[1])
    for Cs in sys.argv[2:]:
        certify(Cs, n=n)
