"""Exact rational lower-bound certificates for the hybrid-height variational constants.

p(beta; F) = 2 - inf { Q_F(f) : f >= 0 even, supp f in [-beta/2, beta/2], int f = 1 },
Q_F(f) = int f^2 + iint f(x) f(y) F(|x-y|) dx dy,

in units of the mean spacing of zeros (bandwidth normalised to log(QT)). Theorem 1.4(a) gives the sharp constant
p(beta_kappa; F_1) with beta_kappa = (2+kappa)/(1+kappa) and F_1(a) = min(a,1).

Majorant shapes (all on [0, beta]):
  'C'      : F(a) = a on [0,1], C on (1,beta]        (flattening + large-sieve constant C above the band)
  'Calpha' : F(a) = a on [0,1], C*a on (1,beta]      (no flattening: diagonal density alpha, constant C)

Method (as in certify.py in this directory, generalised to support beta):
  1. solve the discretised problem (f piecewise constant on n equal cells of [-beta/2, beta/2]) in floating point:
     KKT system M f = mu c if its solution is positive, otherwise a nonnegative QP (SLSQP);
  2. symmetrise, round the heights to integers (scale 1e9), renormalise EXACTLY (int f = 1);
  3. evaluate Q_F(f) in exact rational arithmetic with the exact cell-pair integrals
     int_{cell i} int_{cell j} F(|u-v|) = G2(d+h) - 2 G2(d) + G2(d-h),  G2'' = F(|.|), G2(0) = G2'(0) = 0.
Any admissible f gives p >= 2 - Q(f) (and distinct >= (3 - Q(f))/2); these are rigorous lower bounds. Only step 3
is certified; steps 1-2 just choose the test function.

Run:  OMP_NUM_THREADS=1 taskset -c 0 python3 certify_hybrid.py [n]
"""
import math
import sys
import numpy as np
from fractions import Fraction as Fr


def G2_float(x, C, shape):
    x = np.abs(x)
    if shape == 'C':
        return np.where(x <= 1, x**3 / 6, 1 / 6 + (x - 1) / 2 + C * (x - 1)**2 / 2)
    # 'Calpha': F = C*a on (1, beta]; G2(x) = x^3/6 on [0,1]; beyond: G2'' = C a, G2'(1) = 1/2, G2(1) = 1/6
    # G2(x) = 1/6 + (x-1)/2 + C*( (x^3 - 1)/6 - (x-1)/2 )  [since int_1^x int_1^s C t dt ds = C*((x^3-1)/6 - (x-1)/2)]
    return np.where(x <= 1, x**3 / 6, 1 / 6 + (x - 1) / 2 + C * ((x**3 - 1) / 6 - (x - 1) / 2))


def G2_exact(x, C, shape):
    x = abs(x)
    if x <= 1:
        return x**3 / 6
    if shape == 'C':
        return Fr(1, 6) + (x - 1) / 2 + C * (x - 1)**2 / 2
    return Fr(1, 6) + (x - 1) / 2 + C * ((x**3 - 1) / 6 - (x - 1) / 2)


def matrix(beta, C, n, shape):
    h = beta / n
    d = (np.arange(n)[:, None] - np.arange(n)[None, :]) * h
    M = h * np.eye(n) + (G2_float(d + h, C, shape) - 2 * G2_float(d, C, shape) + G2_float(d - h, C, shape))
    return M, h


def solve_float(beta, C, n, shape):
    M, h = matrix(beta, C, n, shape)
    c = h * np.ones(n)
    f = np.linalg.solve(M, c)
    f /= c @ f
    if f.min() > 0:
        return f, float(f @ M @ f), 'KKT'
    # nonnegative QP on the even half
    from scipy.optimize import minimize
    half = n // 2
    S = np.zeros((n, half))
    for i in range(half):
        S[half - 1 - i, i] = 1.0
        S[half + i, i] = 1.0
    Mh = S.T @ M @ S
    ch = S.T @ c
    g0 = np.full(half, 1.0 / (ch.sum()))
    cons = {'type': 'eq', 'fun': lambda g: ch @ g - 1, 'jac': lambda g: ch}
    r = minimize(lambda g: g @ Mh @ g, g0, jac=lambda g: 2 * Mh @ g, bounds=[(0, None)] * half,
                 constraints=[cons], method='SLSQP', options={'maxiter': 5000, 'ftol': 1e-15})
    g = np.maximum(r.x, 0)
    f = S @ g
    f /= c @ f
    return f, float(f @ M @ f), 'QP'


def exact_Q(m, beta, C, n, shape):
    h = beta / n
    S = sum(m)
    Kd = {}
    for dd in range(-(n - 1), n):
        d = dd * h
        Kd[dd] = G2_exact(d + h, C, shape) - 2 * G2_exact(d, C, shape) + G2_exact(d - h, C, shape)
    diag = sum(x * x for x in m)
    tot = h * diag
    for dd in range(-(n - 1), n):
        corr = sum(m[i] * m[i - dd] for i in range(max(0, dd), min(n, n + dd)))
        tot += Kd[dd] * corr
    return tot / (h * S) ** 2


def certify(beta_str, C_str, n=400, shape='C', label='', scale=10**9):
    beta = Fr(beta_str)
    C = Fr(C_str)
    f, Qf, how = solve_float(float(beta), float(C), n, shape)
    fs = 0.5 * (f + f[::-1])
    m = [max(0, int(round(v * scale))) for v in fs]
    m = [(a + b) // 2 for a, b in zip(m, m[::-1])]
    Q = exact_Q(m, beta, C, n, shape)
    p = 2 - Q
    dist = (3 - Q) / 2
    pf = Fr(int(p * 10**6) - (1 if p < 0 else 0), 10**6)  # floor
    df = Fr(int(dist * 10**6), 10**6)
    # 9-digit values printed as true floors of the exact rationals (math.floor of a Fraction is exact), so that
    # "EXACT p >= x" is a valid inequality.
    p9 = Fr(math.floor(p * 10**9), 10**9)
    d9 = Fr(math.floor(dist * 10**9), 10**9)
    print(f"{label:>10} beta={beta_str:>6} ({float(beta):.4f}) shape={shape:<6} C={C_str:<11} n={n} [{how}]: "
          f"float p={2 - Qf:.7f}; EXACT p >= {float(p9):.9f} (certified >= {float(pf):.6f}); "
          f"distinct >= {float(d9):.9f} (certified >= {float(df):.6f}); min f={min(fs):.4f}", flush=True)
    return p, dist


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    kappas = [("0", "2"), ("1/4", "9/5"), ("1/2", "5/3"), ("1", "3/2"), ("2", "4/3"), ("3", "5/4"),
              ("5", "7/6"), ("10", "12/11")]
    # sharp route (C_T^+ -> 1), Gauss route (C_G R_w -> C_G <= 1.2688), classical large sieve (eta <= 0.01: 4.175)
    for kap, beta in kappas:
        for C in ["1", "12688/10000", "2", "4175/1000"]:
            certify(beta, C, n=n, shape='C', label=f"kappa={kap}")
    # no flattening at all (diagonal density alpha above 1), classical constant
    for kap, beta in kappas:
        for C in ["1", "4175/1000"]:
            certify(beta, C, n=n, shape='Calpha', label=f"kappa={kap}")
