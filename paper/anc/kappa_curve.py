"""NUMERIC (float) curve of the Theorem 1.4 constants p(beta(kappa); F_C) on a fine kappa grid, and the HY26b
single-prime-modulus constants 2 - 1/c*_lambda at lambda = 1/(1+theta) for comparison. Certified values for selected
kappa are in certify_hybrid_n*.log; this file only draws the curve."""
import numpy as np
from certify_hybrid import solve_float

def cstar(lam):
    s = lam / np.sqrt(2)
    return np.sqrt(2) * np.tan(s) / (1 + s * np.tan(s))

print("kappa  beta     p(beta;min(a,1))  p(beta;F_1.2688)  p(beta;F_4.175)  p(beta;F_5.5656)  HY26b(theta=kappa, one prime modulus)")
for k in [0.0, 0.1, 0.25, 0.5, 0.75, 1, 1.5, 2, 3, 4, 5, 7, 10, 20, 50, 100]:
    beta = (2 + k) / (1 + k)
    vals = [2 - solve_float(beta, C, 400, 'C')[1] for C in (1.0, 1.2688, 4.175, 5.5656)]
    lam = 1 / (1 + k)
    hy = 2 - 1 / cstar(lam)
    print(f"{k:6.2f} {beta:.4f}   " + "   ".join(f"{v:.5f}         " for v in vals) + f"   {hy:+.4f}")
