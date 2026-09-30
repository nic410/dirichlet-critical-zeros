"""The extremal problem of the certificate (Section 7.1 of the paper), with exact cell integrals.

  J(f) = int f^2 + int int f(u) f(v) F(|u-v|) du dv,   f >= 0 on [-A/2, A/2],  int f = 1.
  Proportion simple & on-line >= 2 - J(f);  distinct >= (3 - J(f))/2  (any admissible f).

F is the (upper bound for the) family form factor on (0, A], A <= 2:
  shape 'e' : F = C * min(a, 1)                       (uniform majorant; Section 8.2, item (a))
  shape 'd' : F = a on [0,1],  C on (1, A]             (refined majorant F_C of eq. (1.3); Section 8.2, item (b))
  shape 'gue': F = min(a,1)  (= 'd' with C = 1)
  shape 'mont': F = a (Montgomery, only meaningful for A <= 1)

f is piecewise constant on n equal cells; the cell-pair integrals are EXACT via the second
antiderivative G2 of F(|s|):  int_cell_i int_cell_j F(|u-v|) = G2(d+h) - 2 G2(d) + G2(d-h), d=(i-j)h.
So J(f) for the returned step function is exact up to float rounding (checked against mpmath).
Optimisation (nonconvex for C>1): SLSQP from several starts + replicator dynamics; best kept.
"""
import numpy as np, sys, json
from scipy.optimize import minimize

def G2_factory(shape, C):
    def G2(x):
        x = np.abs(np.asarray(x, dtype=float))
        if shape == 'e':
            return np.where(x <= 1, C * x**3 / 6, C / 6 + C * (x - 1) / 2 + C * (x - 1)**2 / 2)
        if shape in ('d', 'gue'):
            CC = 1.0 if shape == 'gue' else C
            return np.where(x <= 1, x**3 / 6, 1 / 6 + (x - 1) / 2 + CC * (x - 1)**2 / 2)
        if shape == 'mont':
            return x**3 / 6
        raise ValueError(shape)
    return G2

def build(A, shape, C, n):
    h = A / n
    G2 = G2_factory(shape, C)
    d = (np.arange(n)[:, None] - np.arange(n)[None, :]) * h
    K = G2(d + h) - 2 * G2(d) + G2(d - h)          # = int int over cell pair (not normalised)
    M = h * np.eye(n) + K                           # J = f^T M f  with f = step heights
    c = h * np.ones(n)                              # int f = c^T f
    return M, c, h

def J_of(f, M):
    return float(f @ M @ f)

def replicator(M, c, x0, iters=20000):
    # minimise x^T M x over simplex {x>=0, c^T x = 1} via replicator dynamics on y = c*x (sum y = 1)
    h = c[0]
    Mt = M / h**2
    y = x0 * h
    y = y / y.sum()
    shift = np.abs(Mt).max() * 2 + 1
    B = shift - Mt
    for _ in range(iters):
        By = B @ y
        y = y * By / (y @ By)
    return y / h

def solve(A, shape, C, n=200, starts=6, seed=0):
    M, c, h = build(A, shape, C, n)
    x = -A / 2 + h * (np.arange(n) + 0.5)
    rng = np.random.default_rng(seed)
    cands = []
    inits = [np.ones(n), np.cos(np.pi * x / A / 1.0001), np.cos(np.sqrt(2) * x / max(A, 1)) , np.maximum(np.cos(np.pi * x / A)**2, 0)]
    for s in range(starts):
        inits.append(np.abs(rng.normal(size=n)) + 0.1)
    cons = [{'type': 'eq', 'fun': lambda f: c @ f - 1, 'jac': lambda f: c}]
    for f0 in inits:
        f0 = f0 / (c @ f0)
        try:
            r = minimize(lambda f: f @ M @ f, f0, jac=lambda f: 2 * M @ f, bounds=[(0, None)] * n,
                         constraints=cons, method='SLSQP', options={'maxiter': 2000, 'ftol': 1e-14})
            f = np.maximum(r.x, 0); f /= c @ f
            cands.append((J_of(f, M), f))
        except Exception as e:
            pass
        f = replicator(M, c, np.maximum(f0, 1e-3), iters=4000)
        f /= c @ f
        cands.append((J_of(f, M), f))
    Jb, fb = min(cands, key=lambda t: t[0])
    return Jb, fb, x

def best_over_A(shape, C, As, n=160):
    out = []
    for A in As:
        J, f, x = solve(A, shape, C, n=n, starts=3)
        out.append((2 - J, A, J))
    return max(out)

if __name__ == '__main__':
    # sanity checks
    J, f, x = solve(1.0, 'mont', 1.0, n=300)
    cmt = 0.5 + 1 / (np.sqrt(2) * np.tan(1 / np.sqrt(2)))
    print(f"A=1 F=a: 2-J = {2-J:.6f}   (Montgomery-Taylor 2-1/cMT... exact {2 - cmt:.6f})")
    J, f, x = solve(2.0, 'gue', 1.0, n=300)
    print(f"A=2 F=min(a,1): 2-J = {2-J:.6f}  (review: 0.9322)")
    sys.stdout.flush()
