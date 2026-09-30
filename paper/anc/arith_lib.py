"""Sieves (numpy) used by ctplus.py: phi, mu up to N; f_empty; P0-signature for fast f_S."""
import numpy as np, math

def spf_sieve(N):
    spf = np.zeros(N + 1, np.int32)
    for p in range(2, int(N**0.5) + 1):
        if spf[p] == 0:
            blk = spf[p*p::p]
            blk[blk == 0] = p
    idx = np.nonzero(spf == 0)[0]
    spf[idx] = idx
    spf[0] = 0; spf[1] = 1
    return spf

def primes_from_spf(spf):
    n = np.arange(len(spf))
    P = np.nonzero((spf == n) & (n >= 2))[0]
    return P

def phi_mu(N, P=None):
    if P is None:
        P = primes_from_spf(spf_sieve(N))
    phi = np.arange(N + 1, dtype=np.float64)
    mu = np.ones(N + 1, np.int8)
    for p in P:
        p = int(p)
        phi[p::p] *= (1.0 - 1.0/p)
        mu[p::p] *= -1
        if p <= N // p:
            mu[p*p::p*p] = 0
    mu[0] = 0
    return phi, mu

def f_empty(N, P):
    f = np.ones(N + 1)
    f[0] = 0.0
    for p in P:
        p = int(p)
        f[p::p] *= (1.0 - 1.0/p - 1.0/(p*p))
    return f

P0 = [2, 3, 5, 7, 11, 13]

def signature(N):
    """sig[n] = sum_i 3^i * min(v_{p_i}(n), 2) for p_i in P0 (3^6 = 729 classes)."""
    n = np.arange(N + 1)
    sig = np.zeros(N + 1, np.int16)
    for i, p in enumerate(P0):
        v = (n % p == 0).astype(np.int16) + (n % (p*p) == 0).astype(np.int16)
        sig += (3**i) * v
    return sig

def factor_table(S):
    """tab[sig] = prod_{p in S} rho_p(v_p) with rho_p(1)=f_in(p)/f0(p), rho_p(2)=f_in(p^2)/f0(p^2)."""
    tab = np.ones(3**len(P0))
    for s in range(3**len(P0)):
        x = s; val = 1.0
        for i, p in enumerate(P0):
            v = x % 3; x //= 3
            if p in S and v > 0:
                c = 1 - 1/p - 1/p**2
                val *= ((p - 2)/(p - 1))/c if v == 1 else ((p - 1)/p)/c
        tab[s] = val
    return tab

GAMMA = 0.5772156649015329

def E_and_c(PMAX=10**7):
    s = np.ones(PMAX + 1, bool); s[:2] = False
    for p in range(2, int(PMAX**0.5) + 1):
        if s[p]: s[p*p::p] = False
    P = np.nonzero(s)[0].astype(np.float64)
    logE = np.sum(np.log1p(-P**-2 - P**-3))
    E_hi = math.exp(logE)
    # tail: sum_{p>X} (p^-2+p^-3) <= 1.01*sum_{p>X} p^-2 <= 1.01*2.52/(X log X)  [pi(y) <= 1.26 y/log y, partial summation];
    # log(1-x) >= -1.01 x for x small
    E_lo = math.exp(logE - 1.03*2.52/(PMAX*math.log(PMAX)))
    c0 = GAMMA + np.sum(np.log(P)*(P**-2 + P**-3)/(1 - P**-2 - P**-3))
    # tail of c0: sum_{p>X} log p (p^-2+p^-3)/(1-..) <= 1.02 sum_{p>X} log p/p^2 <= 1.02*2.04/X  [theta(y) <= 1.02 y]
    c0_tail = 1.02*2.04/PMAX
    return E_lo, E_hi, c0, c0_tail

def cS_of(S, c0):
    return c0 - sum(math.log(p)/(p**3*(p - 1)*(1 - p**-2 - p**-3)) for p in S)

def B_half(S, PMAX=10**7):
    s = np.ones(PMAX + 1, bool); s[:2] = False
    for p in range(2, int(PMAX**0.5) + 1):
        if s[p]: s[p*p::p] = False
    P = np.nonzero(s)[0].astype(np.float64)
    g1 = 1/P + 1/P**2
    g2 = np.zeros_like(P)
    for p in S:
        i = int(np.searchsorted(P, p))
        g1[i] = 1/(p - 1); g2[i] = 1/(p*(p - 1))
    logB = np.sum(np.log1p(g1*P**-0.5 + g2/P))
    # tail p>PMAX: sum (1/p+1/p^2) p^-1/2 <= 1.01 * sum_{p>X} p^-3/2 <= 1.01*3.78/(sqrt(X) log X)
    tail = 1.01*3.78/(math.sqrt(PMAX)*math.log(PMAX))
    return math.exp(logB + tail)
