"""Brute-force re-evaluation (no prefix/suffix sums, no sin^2 expansion) of R^m and R_empty at a few t,
at mp.dps=25, to validate xcheck_Rm.py."""
import time
from fractions import Fraction
import mpmath as mp
from xcheck_common import compute_E, spf_sieve, factor, f_rational

mp.mp.dps = 25
E = compute_E(dps=40, verbose=False)[0]
NMAX = 60000
spf = spf_sieve(NMAX)


def mu_phi(n):
    fac = factor(n, spf)
    mu = 0 if any(a > 1 for _, a in fac) else (-1) ** len(fac)
    ph = 1
    for p, a in fac:
        ph *= (p - 1) * p ** (a - 1)
    return mu, ph


MP = [None] + [mu_phi(n) if n > 1 else (1, 1) for n in range(1, NMAX + 1)][0:]
MP = [None] + [mu_phi(n) if n > 1 else (1, 1) for n in range(1, NMAX + 1)]


def h(y, L, weight):
    if y < 0 or y > L:
        return mp.mpf(0)
    return mp.mpf(1) if weight == 'sharp' else mp.sin(mp.pi * y / L) ** 2


def Rm(weight, N0, q):
    L = mp.log(N0); Iw = L if weight == 'sharp' else L / 2
    eta = mp.mpf(1) / N0
    t = mp.mpf(q.numerator) / q.denominator * eta
    a, b = q.numerator, q.denominator
    tot = mp.mpf(0)
    k = 1
    while 2 * k * a <= b * N0:                 # kt <= 1/2
        u = k * t
        G = mp.mpf(0)
        rlo = max(2, -((-b) // (k * a))); rhi = (b * N0) // (k * a)
        for r in range(rlo, rhi + 1):
            mu, ph = MP[r]
            if mu == -1:
                G += h(mp.log(1 / (u * r)), L, weight) / (mp.mpf(r) ** 2 * ph)
        m = G - h(mp.log(1 / u), L, weight)
        if m > 0:
            tot += mp.mpf(MP[k][1]) / k ** 2 * m
        k += 1
    return tot / (E * Iw)


def R0(weight, N0, q):
    L = mp.log(N0); Iw = L if weight == 'sharp' else L / 2
    a, b = q.numerator, q.denominator
    x = mp.mpf(N0) * b / a
    lo = -((-b) // a); hi = (b * N0) // a
    tot = mp.mpf(0)
    for n in range(max(lo, 1), hi + 1):
        num, den = f_rational(factor(n, spf), frozenset())
        tot += mp.mpf(num) / (den * n) * h(mp.log(x / n), L, weight)
    return tot / (E * Iw)


t0 = time.time()
for weight, N0, qs in [('logsmooth', 1000, [Fraction(3, 10), Fraction(6, 5), Fraction(2), Fraction(133786927, 10**8)]),
                       ('logsmooth', 10000, [Fraction(6, 5), Fraction(5, 2), Fraction(120983691, 10**8)]),
                       ('sharp', 10000, [Fraction(1, 5), Fraction(1, 2), Fraction(99, 100), Fraction(50000109, 10**8)])]:
    for q in qs:
        s = f"{weight:9s} N0={N0:5d} t/eta={float(q):.8f}: R^m = {mp.nstr(Rm(weight, N0, q), 15)}"
        if q.denominator >= 10**8:
            r0 = R0(weight, N0, q)
            s += f"  R_empty = {mp.nstr(r0, 15)}"
        print(s, flush=True)
print(f"time {time.time()-t0:.1f}s")
