#!/usr/bin/env python3
r"""
certify_constants_arb.py -- interval-arithmetic (Arb) enclosures of the arithmetic constants of Table tab:constants

Certifies, with explicit tail bounds, every constant of Table tab:constants that is used in a proof:
    E       = prod_p (1 - p^-2 - p^-3)                      (lem:WH; H, C_G, R_S)
    C_G     = 6/(pi^2 E)                                     (thm:gauss, thm:fixed: C_G <= 1.2688, C_G < 1.268774)
    c_phi   = gamma - zeta'(2)/zeta(2) = 12 log A - log(2 pi) (lem:harm)
    B_phi   = zeta(3/2)/zeta(3)                              (lem:harm; 4 B_phi pi^2/6 <= 14.31 in lem:Rwlog)
    Z       = zeta(2) zeta(3)/zeta(6) = sum mu^2(d)/(d phi(d)) (tail bounds; lem:M2, lem:C)
    S2      = sum_r mu^2(r)/(r^2 phi(r)) = prod_p (1 + 1/(p^2 (p-1)))            (lem:Omega(a): <= 1.34)
    sigma0- = sum_{mu(r)=-1} 1/(r^2 phi(r))                  (lem:Omega(d): < 0.33 < 1)
    sigma1- = sum_{mu(r)=-1} log r/(r^2 phi(r))              (lem:Omega(e), lem:CTlimit: < 0.27)
    c_empty = gamma + sum_p (p^-2 + p^-3) log p/(1 - p^-2 - p^-3)                 (lem:fS(iii))
    D       = max_S (c_empty - c_S) = sum_p log p/(p^3 (p-1)(1 - p^-2 - p^-3))  (lem:fS(iii): < 0.168)
    B       = prod_p (1 + p^{-1/2}/(p-1) + p^{-1}/(p(p-1)))  (lem:fS(iii): < 3.73)
    delta_P0 = prod_{p>13} (1 + 2/(p^3 (p-1))) - 1           (prop:CTfixed: < 5.83e-5)
and the derived inequalities  4B/E < 31.14  and  c_empty + 4B/E < 32.6  with the stated B < 3.73 (lem:CTlimit).

E, c_empty, B, delta_P0, sigma0- and the s_half sum are computed by ctplus_arb.global_constants (same code and the
same tail bounds as the C_T^+ certificates).  The additional tails used here:
  S2      : prod_{p>P}(1 + 1/(p^2(p-1))) <= exp(sum_{n>P} 2/n^3) <= exp(1/P^2);
  sigma0- : lower bound = the partial sum (all terms >= 0);
  sigma1- : sum_{r>R0} mu^2(r) log r/(r^2 phi(r)) <= (2/e) sum_{r>R0} mu^2(r) r^{1/2}/(r^2 phi(r))
            <= (2/e)(5/3) Z R0^{-3/2}   (log r <= (2/e) r^{1/2}; the s_half tail of ctplus_arb.py, see README);
  D       : sum_{p>P} log p/(p^3(p-1)(1-p^-2-p^-3)) <= (8/5) sum_{n>P} 2 log n/n^4 <= (16/5)(3 log P + 1)/(9 P^3).
Every decision is taken on exact rational endpoints (fmpq), as in ctplus_arb.py.

usage:  python3 certify_constants_arb.py [--Pc 10000000] [--R0 1000000]
"""
import sys, os, time, argparse, platform
import flint
from flint import arb, fmpq, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ctplus_arb import ub, lb, A, interval, fdec, phi_mu, primes_upto, global_constants, PREC
import numpy as np

ctx.prec = PREC
T00 = time.time()


def log(msg):
    print(f"[{time.time() - T00:6.1f}s] {msg}", flush=True)


def enc(x, d=10):
    return f"[{fdec(lb(x), d)}, {fdec(ub(x), d)}]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--Pc', type=int, default=10 ** 7)
    ap.add_argument('--R0', type=int, default=10 ** 6)
    a = ap.parse_args()
    Pc, R0 = a.Pc, a.R0
    log(f"certify_constants_arb: Pc={Pc} R0={R0} prec={PREC}")
    log(f"environment: python {platform.python_version()}, python-flint {flint.__version__} (FLINT {flint.__FLINT_VERSION__}), "
        f"numpy {np.__version__}, {platform.machine()} {platform.system()}")
    phi, mu = phi_mu(max(R0, 100) + 10)
    K = global_constants(Pc, R0, phi, mu)
    E, c0, B, dP0, G, c_phi, B_phi = (K[k] for k in ('E', 'c0', 'B', 'dP0', 'G', 'c_phi', 'B_phi'))
    pi = arb.pi()
    one = arb(1)
    CG = 6 / (pi * pi * E)
    Z = arb(2).zeta() * arb(3).zeta() / arb(6).zeta()

    # sigma0- lower bound and sigma1- (squarefree r <= R0 with mu(r) = -1)
    rs = K['rs_neg'].tolist()
    s0 = arb(0); s1 = arb(0)
    for r in rs:
        nr = A(fmpq(1, r * r * int(phi[r])))
        s0 += nr
        s1 += nr * arb(r).log()
    sig0 = interval(lb(s0), ub(G))
    tail1 = 2 / one.exp() * A(fmpq(5, 3)) * Z / arb(R0) ** fmpq(3, 2)
    sig1 = s1 + interval(fmpq(0), ub(tail1))

    # S2 and D over primes p <= Pc
    pr = primes_upto(Pc).tolist()
    S2 = arb(1); D = arb(0)
    for p in pr:
        p3 = p * p * p
        S2 *= A(fmpq(p3 - p * p + 1, p3 - p * p))
        D += arb(p).log() / A(fmpq((p - 1) * (p3 - p - 1)))     # = log p/(p^3 (p-1)(1-p^-2-p^-3))
    P = arb(Pc)
    S2 = S2 * interval(fmpq(1), ub((one / (P * P)).exp()))
    D = D + interval(fmpq(0), ub(A(fmpq(16, 5)) * (3 * P.log() + 1) / (9 * P ** 3)))

    rows = [
        ("E = prod_p(1-p^-2-p^-3)", E, 12),
        ("C_G = 6/(pi^2 E)", CG, 12),
        ("c_phi = gamma - zeta'(2)/zeta(2)", c_phi, 12),
        ("B_phi = zeta(3/2)/zeta(3)", B_phi, 12),
        ("4 B_phi pi^2/6", 4 * B_phi * pi * pi / 6, 10),
        ("Z = zeta(2)zeta(3)/zeta(6)", Z, 12),
        ("S2 = sum mu^2(r)/(r^2 phi(r))", S2, 10),
        ("sigma_0^- = sum_{mu(r)=-1} 1/(r^2 phi(r))", sig0, 10),
        ("sigma_1^- = sum_{mu(r)=-1} log r/(r^2 phi(r))", sig1, 10),
        ("c_empty", c0, 10),
        ("max_S (c_empty - c_S)", D, 10),
        ("B", B, 8),
        ("delta_P0", dP0, 12),
    ]
    for name, x, d in rows:
        log(f"{name:48s} in {enc(x, d)}")

    B_st = A(fmpq(373, 100))
    checks = [
        ("E >= 0.47914 (Lean Ecal_ge_047914)", lb(E) >= fmpq(47914, 10 ** 5)),
        ("C_G <= 1.2688", ub(CG) <= fmpq(12688, 10 ** 4)),
        ("C_G < 1.268774", ub(CG) < fmpq(1268774, 10 ** 6)),
        ("C_G < 1.26877394", ub(CG) < fmpq(126877394, 10 ** 8)),
        ("C_G > 1.2687738 (so C_G = 1.2687739...)", lb(CG) > fmpq(12687738, 10 ** 7)),
        ("4 B_phi pi^2/6 <= 14.31", ub(4 * B_phi * pi * pi / 6) <= fmpq(1431, 100)),
        ("B_phi < 2.174", ub(B_phi) < fmpq(2174, 1000)),
        ("Z <= 1.95", ub(Z) <= fmpq(195, 100)),
        ("S2 <= 1.34", ub(S2) <= fmpq(134, 100)),
        ("sigma_0^- < 0.33", ub(sig0) < fmpq(33, 100)),
        ("sigma_1^- < 0.27", ub(sig1) < fmpq(27, 100)),
        ("c_empty < 1.411", ub(c0) < fmpq(1411, 1000)),
        ("max_S(c_empty - c_S) < 0.168", ub(D) < fmpq(168, 1000)),
        ("B < 3.73", ub(B) < fmpq(373, 100)),
        ("delta_P0 < 5.83e-5", ub(dP0) < fmpq(583, 10 ** 7)),
        ("4 B/E < 31.14 with the stated B < 3.73", ub(4 * B_st / E) < fmpq(3114, 100)),
        ("c_empty + 4B/E < 32.6 with the stated B < 3.73", ub(c0 + 4 * B_st / E) < fmpq(326, 10)),
    ]
    ok = True
    for name, v in checks:
        log(f"check {name:52s} {'OK' if v else 'FAILED'}")
        ok = ok and v
    assert ok
    log(f"SUMMARY: all {len(checks)} inequalities CERTIFIED; total time {time.time() - T00:.0f}s")


if __name__ == '__main__':
    main()
