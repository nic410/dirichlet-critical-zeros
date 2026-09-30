"""Task 2 (sharp weight) + Task 3.
Sharp: h = 1 on [0,L], I_w = L. For x in (m, m+1), m = A*N0 + b, window n in [A+1, m]:
  R_S = (E L)^{-1} (F_S(m) - F_S(A)),  F_S(m) = sum_{n<=m} f_S(n)/n.
F_S computed in exact fixed point (2^-SHIFT units, floor per term => abs error < N*2^-SHIFT).
"""
import sys, time
from fractions import Fraction
from multiprocessing import Pool
import numpy as np
import mpmath as mp
from xcheck_common import all_subsets, label, spf_sieve, factor, f_rational, compute_E, f_over_n_float_array

N = 10**5
SHIFT = 256
N0S = (100, 1000, 10000)
mp.mp.dps = 50

spf = spf_sieve(N)
FAC = [None, []] + [factor(n, spf) for n in range(2, N + 1)]


def work(S):
    F = [0] * (N + 1)
    acc = 0
    one = 1 << SHIFT
    for n in range(1, N + 1):
        num, den = f_rational(FAC[n], S)
        acc += (num << SHIFT) // (den * n)
        F[n] = acc
    res = {}
    for N0 in N0S:
        best = []  # (D, m)
        Dmax, mmax = -1, None
        D2, m2 = -1, None
        for m in range(1, N):
            D = F[m] - F[m // N0]
            if D > Dmax:
                D2, m2 = Dmax, mmax
                Dmax, mmax = D, m
            elif D > D2:
                D2, m2 = D, m
        res[N0] = dict(Dmax=Dmax, mmax=mmax, D2=D2, m2=m2, F_N0=F[N0], F_N0m1=F[N0 - 1])
    # float check value
    return S, res, F[N]


if __name__ == "__main__":
    t0 = time.time()
    E, _ = compute_E(dps=50, verbose=False)
    subsets = all_subsets()
    with Pool(6) as pool:
        out = pool.map(work, subsets)
    ulp = mp.mpf(2) ** (-SHIFT)
    print(f"# sharp weight, N={N}, fixed point 2^-{SHIFT}; E={mp.nstr(E, 25)}; time {time.time()-t0:.1f}s")
    named = [frozenset(), frozenset({13}), frozenset({11}), frozenset({11, 13}), frozenset({7}), frozenset({2})]
    table = {}
    for S, res, FN in out:
        # double-precision consistency check of prefix sum at N
        v = f_over_n_float_array(N, S)
        assert abs(float(mp.mpf(FN) * ulp) - v.sum()) < 1e-9, (S, float(mp.mpf(FN)*ulp), v.sum())
        for N0 in N0S:
            r = res[N0]
            L = mp.log(N0)
            val = mp.mpf(r['Dmax']) * ulp / (E * L)
            val2 = mp.mpf(r['D2']) * ulp / (E * L)
            table[(N0, S)] = (val, r['mmax'], val2, r['m2'], r)
    for N0 in N0S:
        L = mp.log(N0)
        print(f"\n== sharp, N0={N0} (L=log N0) ==")
        allS = sorted(((table[(N0, S)][0], S) for S in subsets), key=lambda z: -z[0])
        for val, S in allS[:5]:
            v, m, v2, m2, r = table[(N0, S)]
            print(f"  top: S1={label(S):16s} sup R = {mp.nstr(v, 20)} on x in ({m},{m+1}) i.e. t/eta in ({mp.nstr(mp.mpf(N0)/(m+1),10)},{mp.nstr(mp.mpf(N0)/m,10)});"
                  f" runner-up piece m={m2}: {mp.nstr(v2, 15)}")
        print(f"  min over S1 of sup: {mp.nstr(allS[-1][0], 15)} at {label(allS[-1][1])}")
        for S in named:
            v, m, v2, m2, r = table[(N0, S)]
            print(f"  named S1={label(S):10s} sup R = {mp.nstr(v, 20)}  (piece m={m}, t/eta->{mp.nstr(mp.mpf(N0)/(m+1),8)}+);"
                  f"  runner-up m={m2}: {mp.nstr(v2, 15)}")
        # all 64 compact
        print("  all 64 (S1: sup R, argmax piece m):")
        for S in subsets:
            v, m, *_ = table[(N0, S)]
            print(f"    {label(S):18s} {mp.nstr(v, 16):>20s} m={m}")
        # Task 3 pointwise at x = N0 for S = {} (fixed-point + exact rational)
        r = table[(N0, frozenset())][4]
        pw_fp = mp.mpf(r['F_N0']) * ulp / (E * L)
        Fr = Fraction(0)
        for n in range(1, N0 + 1):
            num, den = f_rational(FAC[n], frozenset())
            Fr += Fraction(num, den * n)
        pw_ex = (mp.mpf(Fr.numerator) / Fr.denominator) / (E * L)
        print(f"  TASK3 pointwise x=N0 S1={{}}: (E L)^-1 sum_(n<=N0) f/n = {mp.nstr(pw_ex, 25)}  (exact rational sum; fixed-point gives {mp.nstr(pw_fp, 25)})")
        print(f"        sum_(n<=N0) f/n = {mp.nstr(mp.mpf(Fr.numerator)/Fr.denominator, 25)};  x->N0^- value (n<=N0-1) = {mp.nstr(mp.mpf(r['F_N0m1'])*ulp/(E*L), 25)}")
    print(f"\ntotal time {time.time()-t0:.1f}s")
