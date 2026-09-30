"""Exact rational certificates for the dyadic family w = 1_[1/2,1] of Corollary 1.5 (classical route, C_cl = 8/(3 Ec)).

C_cl(dyadic) = w_max/(Ec * int_0^1 u w(u) du) = 1/(Ec * 3/8) = 8/(3 Ec); with the certified Ec >= 0.47914533
(Tables 3 and 4 of the paper) this is <= 5.565466 <= 55657/10000, which is the value used below (a valid upper bound;
p(beta; F_C) is nonincreasing in C).

Run:  OMP_NUM_THREADS=1 taskset -c 1 python3 certify_dyadic.py [n]
"""
import sys
from certify_hybrid import certify

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    print("# C_cl(dyadic) = 8/(3*Ec) with Ec in [0.47914533,0.47914535] => C_cl <= 8/(3*0.47914533) = 5.5654652... <= 5.565466; we use 55657/10000")
    for kap, beta in [("0", "2"), ("1/2", "5/3"), ("1", "3/2"), ("2", "4/3"), ("3", "5/4"), ("5", "7/6"), ("10", "12/11")]:
        certify(beta, "55657/10000", n=n, shape='C', label=f"kappa={kap}")
