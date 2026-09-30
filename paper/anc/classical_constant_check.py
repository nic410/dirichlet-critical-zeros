"""Exact check of the classical-route constant C_cl(w) = w_max/(Ec * int_0^1 u w(u) du) used in Theorem 1.4(c), the
kappa-table after Theorem 1.4 and Corollary 1.5 of the paper.

For w = 1_[eta,1]:   C_cl = 2/(Ec (1 - eta^2));   for the dyadic w = 1_[1/2,1]:   C_cl = 8/(3 Ec).
Uses the certified lower bound Ec >= 0.47914533 of the paper (Table 3). Exact rationals only.
Run:  python classical_constant_check.py
"""
import math
from fractions import Fraction as Fr


def ceil_dec(q, d):
    # printed upper bounds are exact ceilings of the exact rationals
    return float(Fr(math.ceil(q * 10**d), 10**d))


E_lo = Fr(47914533, 10**8)
C_tab = Fr(4175, 1000)
for eta in [Fr(1, 100), Fr(146, 10000), Fr(1469, 100000), Fr(147, 10000)]:
    C = 2 / (E_lo * (1 - eta**2))
    print(f"w=1_[eta,1], eta={float(eta):.5f}: C_cl <= {ceil_dec(C, 9):.9f}   (<= 4.175: {C <= C_tab})")
# threshold: 2/(E_lo(1-eta^2)) = 4.175  <=>  eta^2 = 1 - 2/(4.175 E_lo)
eta2 = 1 - Fr(2) / (C_tab * E_lo)
# floor of sqrt(eta2) to 7 decimals, exactly: largest k with k^2 <= eta2 * 10^14
k = math.isqrt(math.floor(eta2 * 10**14))
print(f"largest eta with C_cl <= 4.175 (using Ec >= 0.47914533): {float(Fr(k, 10**7)):.7f} (rounded down)")
Cd = Fr(8, 3) / E_lo
print(f"dyadic: C_cl = 8/(3 Ec) <= {ceil_dec(Cd, 7):.7f}   (<= 5.5657: {Cd <= Fr(55657, 10000)})")
