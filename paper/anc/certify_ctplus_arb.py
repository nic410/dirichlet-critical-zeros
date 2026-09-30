#!/usr/bin/env python3
"""Assemble the interval certificates for C_T^+ (ctplus_arb.py) and R_w (rw_arb.py); certify p(C) at the certified bounds.

For each of the six runs ctplus_arb_{sharp,lsmooth}_{100,1000,10000}.json (written by ctplus_arb.py into the
same directory as this script, or into --dir), read the CERTIFIED exact rational upper bound Cbar >= C_T^+(w),
round it UP to 5 decimals (C5) and to 4 decimals (C4), and evaluate the exact rational certificate
p(C) >= 2 - Q_{F_C}(f) of certify.py (same directory) at C5 and C4 with n = 1600 cells.  Since p is
nonincreasing in C (lem:pLip), p(C_T^+(w)) >= p(C5) >= the printed value.

usage:  python3 certify_ctplus_arb.py [--dir DIR] [--n 1600]
"""
import os, sys, json, math, argparse, time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from certify import certify      # exact rational p(C) certificate (unchanged copy of the paper's certify.py)


def ceil_dec(q, d):
    return Fr(math.ceil(q * 10 ** d), 10 ** d)


def floor_dec(q, d):
    # printed lower bounds are exact floors (and printed upper bounds exact ceilings) of the exact rationals
    return Fr(math.floor(q * 10 ** d), 10 ** d)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dir', default=HERE)
    ap.add_argument('--n', type=int, default=1600)
    a = ap.parse_args()
    t0 = time.time()
    rows = []
    for kind in ['sharp', 'lsmooth']:
        for N0 in [100, 1000, 10000]:
            fn = os.path.join(a.dir, f'ctplus_arb_{kind}_{N0}.json')
            d = json.load(open(fn))
            assert d['n_subsets'] == 64, 'all 64 sets S1 must be present'
            Cbar = Fr(d['Cbar'])
            lo = Fr(d['supRS_lower'])
            rows.append((kind, N0, Cbar, lo, d))
    print("Certified upper bounds C_T^+(w) <= Cbar (prop:CTfixed, all 64 S1, far field, slack), Arb interval arithmetic:")
    print(f"{'weight':8s} {'eta':>7s} {'sup_t R_empty(t) in (cert.)':>28s} {'mu^- region <=':>15s} {'C_T^+ <= Cbar':>14s} "
          f"{'C5':>8s} {'C4':>7s}  slack        time")
    for kind, N0, Cbar, lo, d in rows:
        hi = Fr(d['supRS_empty_upper'])
        mr = Fr(d['mu_region_max'])
        print(f"{kind:8s} 1/{N0:<5d} [{float(floor_dec(lo, 8)):.8f}, {float(ceil_dec(hi, 8)):.8f}] "
              f"{float(ceil_dec(mr, 6)):15.6f} {float(ceil_dec(Cbar, 9)):14.9f} "
              f"{float(ceil_dec(Cbar, 5)):8.5f} {float(ceil_dec(Cbar, 4)):7.4f}  {float(Fr(d['slack'])):.3e}  {d['seconds']}s")
    print("  (mu^- region: max over S1 of sup (R_S1 + R^m) over t < eta (sharp) resp. t < 3 eta (log-smooth); "
          "the maximiser of sup_t R_S1 is S1 = {} in every case)")
    for kind, N0, Cbar, lo, d in rows:
        assert d['supRS_lower_S'] == [] and d['argmax_S'] == []
    print()
    print(f"Exact rational p(C) certificates at the rounded-up bounds (certify.py, n = {a.n}):")
    for kind, N0, Cbar, lo, d in rows:
        for dec in (5, 4):
            C = ceil_dec(Cbar, dec)
            print(f"[{kind} eta=1/{N0}, C{dec}] ", end='', flush=True)
            certify(f"{C.numerator}/{C.denominator}", n=a.n)
    # R_w (Gauss route, Theorem thm:fixed(iii)): rw_arb.py
    print()
    print("Certified upper bounds for R_w (log-smooth weight; rw_arb.py) and C_w = C_G R_w:")
    print(f"{'eta':>8s} {'R_w >= (cert.)':>15s} {'R_w <= Rbar':>13s} {'C_G R_w <=':>12s} {'C4':>7s}  hypothesis in the text")
    hyp = {1000: ('1.0599', '1.3448'), 10000: ('1.0289', '1.3055'), 100000: ('1.0159', '1.2890')}
    rws = []
    for N0 in [1000, 10000, 100000]:
        d = json.load(open(os.path.join(a.dir, f'rw_arb_lsmooth_{N0}.json')))
        Rbar, CGR, lo = Fr(d['Rbar']), Fr(d['CGR_ub']), Fr(d['R_lower'])
        hR, hC = hyp[N0]
        ok = Rbar <= Fr(hR) and CGR <= Fr(hC)
        rws.append((N0, CGR))
        print(f"  1/{N0:<6d} {float(floor_dec(lo, 7)):15.7f} {float(ceil_dec(Rbar, 9)):13.9f} {float(ceil_dec(CGR, 9)):12.9f} "
              f"{float(ceil_dec(CGR, 4)):7.4f}  R_w <= {hR}, C_G R_w <= {hC}: {'holds' if ok else 'FAILS'}")
    for N0, CGR in rws:
        C = ceil_dec(CGR, 4)
        print(f"[Gauss route, lsmooth eta=1/{N0}, C_G R_w <= C4] ", end='', flush=True)
        certify(f"{C.numerator}/{C.denominator}", n=a.n)
    print(f"# total time {time.time() - t0:.0f}s")


if __name__ == '__main__':
    main()
