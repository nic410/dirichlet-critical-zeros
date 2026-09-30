"""Independent cross-check helpers (written from the definitions only).

f_S multiplicative:
  p not in S : f(p^a) = 1 - 1/p - 1/p^2          (a >= 1)
  p in S     : f(p) = (p-2)/(p-1), f(p^a) = (p-1)/p (a >= 2)
"""
import itertools
import numpy as np
import mpmath as mp

SMALLP = (2, 3, 5, 7, 11, 13)


def all_subsets():
    out = []
    for k in range(len(SMALLP) + 1):
        for c in itertools.combinations(SMALLP, k):
            out.append(frozenset(c))
    return out


def label(S):
    return "{" + ",".join(str(p) for p in sorted(S)) + "}"


def spf_sieve(N):
    """smallest prime factor for 0..N (python list)."""
    spf = np.zeros(N + 1, dtype=np.int64)
    for i in range(2, int(N ** 0.5) + 1):
        if spf[i] == 0:
            blk = spf[i * i::i]
            blk[blk == 0] = i
            spf[i * i::i] = blk
    idx = np.arange(N + 1)
    spf[(spf == 0)] = idx[(spf == 0)]
    return spf.tolist()


def factor(n, spf):
    out = []
    while n > 1:
        p = spf[n]
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        out.append((p, a))
    return out


def f_rational(fac, S):
    """exact f_S(n) as (num, den) from factorisation list."""
    num = 1
    den = 1
    for p, a in fac:
        if p in S:
            if a == 1:
                num *= p - 2
                den *= p - 1
            else:
                num *= p - 1
                den *= p
        else:
            num *= p * p - p - 1
            den *= p * p
    return num, den


def f_over_n_float_array(N, S):
    """double-precision array v[n] = f_S(n)/n for n=0..N (v[0]=0).
    f_S = f_empty * prod_{p in S, p|n} (f_S(p^a)/g_p), g_p = 1-1/p-1/p^2."""
    isp = np.ones(N + 1, dtype=bool)
    isp[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if isp[i]:
            isp[i * i::i] = False
    primes = np.nonzero(isp)[0]
    f = np.ones(N + 1)
    for p in primes:
        p = int(p)
        f[p::p] *= 1.0 - 1.0 / p - 1.0 / (p * p)
    for p in S:
        g = 1.0 - 1.0 / p - 1.0 / (p * p)
        r1 = ((p - 2.0) / (p - 1.0)) / g
        r2 = ((p - 1.0) / p) / g
        mult = np.ones(N + 1)
        mult[p::p] = r1
        if p * p <= N:
            mult[p * p::p * p] = r2
        f *= mult
    v = np.zeros(N + 1)
    v[1:] = f[1:] / np.arange(1, N + 1, dtype=np.float64)
    return v


def compute_E(dps=50, P0=1000, K=60, verbose=True):
    """E = prod_p (1 - p^-2 - p^-3).
    log(1 - x^2 - x^3) = -sum_{k>=2} s_k x^k / k, s_k = power sums of roots of y^3 = y + 1
    (s_0=3, s_1=0, s_2=2, s_k = s_{k-2} + s_{k-3}).
    E = prod_{p<=P0}(...) * exp(-sum_{k=2}^K s_k/k * (P(k) - sum_{p<=P0} p^-k)),
    P = prime zeta.  Truncation error (k > K, p > P0) bounded by
      sum_{n>P0} sum_{k>K} (1.3248^k + 2*0.87^k)/k n^-k <= 3 * sum_{n>P0} (1.3248/n)^{K+1}/(1-1.3248/n).
    """
    with mp.workdps(dps + 10):
        primes = [p for p in range(2, P0 + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
        head = mp.mpf(1)
        for p in primes:
            head *= 1 - mp.mpf(p) ** -2 - mp.mpf(p) ** -3
        s = [3, 0, 2]
        while len(s) <= K + 1:
            s.append(s[-2] + s[-3])
        tail = mp.mpf(0)
        for k in range(2, K + 1):
            Pk = mp.primezeta(k) - mp.fsum(mp.mpf(p) ** -k for p in primes)
            tail += mp.mpf(s[k]) / k * Pk
        E = head * mp.exp(-tail)
        # bound on truncation
        q = mp.mpf('1.3248') / P0
        # sum_{n>P0} 3*(1.3248/n)^{K+1}/(K+1)/(1-q) <= 3/(K+1)/(1-q) * 1.3248^{K+1} * P0^{-K}/K
        bound = 3 / mp.mpf(K + 1) / (1 - q) * mp.mpf('1.3248') ** (K + 1) * mp.mpf(P0) ** (-K) / K
        if verbose:
            print(f"E computed with P0={P0}, K={K}, dps={dps}; truncation bound on log E < {mp.nstr(bound, 3)}")
    return E, bound
