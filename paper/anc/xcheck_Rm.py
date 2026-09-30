"""Task 4: R^m(t) = (E I_w)^{-1} sum_k phi(k)/k^2 m~(kt),
m~(u) = ( sum_{mu(r)=-1, r<=RMAX} nu_r w~(u r) - w~(u) )_+,  nu_r = 1/(r^2 phi(r)),  w~(u) = h(log(1/u)).
t = (t/eta) * eta with t/eta = a/b rational -> r-window [b/(k a), b N0/(k a)] computed in exact integer arithmetic.
m~(kt) = 0 once kt > 1/2 (no r >= 2 fits), so k <= floor(b N0/(2a)).
Double precision.  r-sum truncated at RMAX = 1e6 (for N0 <= 1e4 and t/eta >= 0.01 every window has 1/u <= 1e6,
so the truncation is in fact inactive; tail sum_{r>1e6} nu_r < 1e-12 anyway).
"""
import time
from fractions import Fraction
import numpy as np
import mpmath as mp
from xcheck_common import compute_E, f_over_n_float_array

mp.mp.dps = 30
E = float(compute_E(dps=40, verbose=False)[0])
RMAX = 10**6
KMAX = 10**6

t0 = time.time()
# sieve mu, phi up to 1e6
M = max(RMAX, KMAX)
phi = np.arange(M + 1, dtype=np.int64)
mu = np.ones(M + 1, dtype=np.int64)
isp = np.ones(M + 1, dtype=bool); isp[:2] = False
for i in range(2, int(M ** 0.5) + 1):
    if isp[i]:
        isp[i * i::i] = False
for p in np.nonzero(isp)[0]:
    p = int(p)
    phi[p::p] -= phi[p::p] // p
    mu[p::p] *= -1
    if p * p <= M:
        mu[p * p::p * p] = 0
mu[0] = 0
r = np.arange(RMAX + 1)
nu = np.zeros(RMAX + 1)
sel = (mu[:RMAX + 1] == -1)
nu[sel] = 1.0 / (r[sel].astype(np.float64) ** 2 * phi[:RMAX + 1][sel].astype(np.float64))
logr = np.zeros(RMAX + 1); logr[1:] = np.log(r[1:])
kk = np.arange(KMAX + 1)
wk = np.zeros(KMAX + 1); wk[1:] = phi[1:KMAX + 1] / (kk[1:].astype(np.float64) ** 2)
print(f"sieve done {time.time()-t0:.1f}s; sum nu_r (mu=-1, r<=1e6) = {nu.sum():.15f}; tail bound sum_(r>1e6) 1/(r^2 phi(r)) <~ {2.0/RMAX**2:.1e}")


def suffix(a):
    """T[i] = sum_{j>=i} a[j], T has length len(a)+1."""
    T = np.zeros(len(a) + 1)
    T[:-1] = np.cumsum(a[::-1])[::-1]
    return T


class RM:
    def __init__(self, weight, N0):
        self.weight, self.N0 = weight, N0
        self.L = np.log(N0); self.th = 2 * np.pi / self.L
        self.Iw = self.L if weight == 'sharp' else self.L / 2
        self.T0 = suffix(nu)
        if weight == 'logsmooth':
            self.Tc = suffix(nu * np.cos(self.th * logr))
            self.Ts = suffix(nu * np.sin(self.th * logr))
        self.f0 = None

    def value(self, q):
        """q = t/eta as Fraction."""
        a, b, N0 = q.numerator, q.denominator, self.N0
        K = (b * N0) // (2 * a)
        k = np.arange(1, K + 1, dtype=np.int64)
        ka = k * a
        assert b * N0 < 2**62 and (K * a) < 2**62
        hi = np.minimum((b * N0) // ka, RMAX)
        lo = np.maximum(-((-b) // ka), 1)
        ok = hi >= lo
        lo_c = np.where(ok, lo, 1); hi_c = np.where(ok, hi, 0)
        D0 = np.where(ok, self.T0[lo_c] - self.T0[hi_c + 1], 0.0)
        inw = (ka >= b) & (ka <= b * N0)            # u = kt in [eta, 1]
        Y = np.log(float(b * N0)) - np.log(ka.astype(np.float64))   # log(1/u)
        if self.weight == 'sharp':
            G = D0
            w = inw.astype(np.float64)
        else:
            Dc = np.where(ok, self.Tc[lo_c] - self.Tc[hi_c + 1], 0.0)
            Ds = np.where(ok, self.Ts[lo_c] - self.Ts[hi_c + 1], 0.0)
            G = 0.5 * (D0 - np.cos(self.th * Y) * Dc - np.sin(self.th * Y) * Ds)
            w = np.where(inw, np.sin(np.pi * Y / self.L) ** 2, 0.0)
        mt = np.maximum(G - w, 0.0)
        return float(np.dot(wk[1:K + 1], mt)) / (E * self.Iw)

    def R_empty(self, q):
        """R_{empty}(t) pointwise (closed window x/N0 <= n <= x), x = N0 b/a."""
        a, b, N0 = q.numerator, q.denominator, self.N0
        hi = (b * N0) // a; lo = max(-((-b) // a), 1)
        if self.f0 is None or len(self.f0) <= hi:
            self.f0 = f_over_n_float_array(max(hi, 10**5), frozenset())
        n = np.arange(lo, hi + 1)
        v = self.f0[lo:hi + 1]
        if self.weight == 'sharp':
            return v.sum() / (E * self.L)
        X = np.log(N0 * b / a)
        return float(np.sum(v * np.sin(np.pi * (X - np.log(n)) / self.L) ** 2)) / (E * self.Iw)


def fr(x, den=10**6):
    return Fraction(round(x * den), den)


for weight, N0, pts in [('logsmooth', 10000, [0.3, 0.5, 0.8, 1.0, 1.2, 1.5, 2.0, 2.5]),
                        ('logsmooth', 1000, [0.3, 0.5, 0.8, 1.0, 1.2, 1.5, 2.0, 2.5]),
                        ('sharp', 10000, [0.2, 0.5, 0.9, 0.99])]:
    ts = time.time()
    obj = RM(weight, N0)
    print(f"\n== R^m, weight={weight}, N0={N0} ==")
    for p in pts:
        q = Fraction(p).limit_denominator(1000)
        v = obj.value(q)
        line = f"  t/eta={p:<5}: R^m = {v:.12e}"
        if weight == 'sharp':
            vl = obj.value(q * Fraction(10**9 - 1, 10**9)); vr = obj.value(q * Fraction(10**9 + 1, 10**9))
            line += f"   (limits: t/eta*(1-1e-9) -> {vl:.12e}, t/eta*(1+1e-9) -> {vr:.12e})"
        print(line)
    # scan t/eta in [0.01, 6]: log-spaced coarse grid, then refinement around the best
    grid = np.exp(np.linspace(np.log(0.01), np.log(6.0), 3001))
    vals = np.array([obj.value(fr(g)) for g in grid])
    i = int(np.argmax(vals))
    print(f"  coarse scan (3001 log-spaced pts): max R^m = {vals[i]:.12e} at t/eta = {grid[i]:.6f}; "
          f"R^m(0.01) = {vals[0]:.6e}, R^m(6) = {vals[-1]:.6e}")
    # top-5 distinct local maxima of coarse scan
    lm = np.nonzero((vals[1:-1] > vals[:-2]) & (vals[1:-1] >= vals[2:]))[0] + 1
    lm = sorted(lm, key=lambda j: -vals[j])[:5]
    print("  coarse local maxima: " + ", ".join(f"{vals[j]:.6e}@{grid[j]:.5f}" for j in lm))
    lo_, hi_ = grid[max(i - 3, 0)], grid[min(i + 3, len(grid) - 1)]
    fine = np.linspace(lo_, hi_, 4001)
    fv = np.array([obj.value(fr(g, 10**8)) for g in fine])
    j = int(np.argmax(fv))
    qbest = fr(fine[j], 10**8)
    Rm = fv[j]
    R0 = obj.R_empty(qbest)
    print(f"  refined scan (4001 pts in [{lo_:.5f},{hi_:.5f}]): sup R^m ~= {Rm:.12e} at t/eta = {fine[j]:.8f}")
    print(f"  at that point: R_empty = {R0:.12f}, R_empty + R^m = {R0 + Rm:.12f}")
    if weight == 'sharp':
        # also sharp: sup of R_empty + R^m over the coarse grid
        tot = np.array([obj.value(fr(g)) + obj.R_empty(fr(g)) for g in grid[::3]])
        jj = int(np.argmax(tot))
        print(f"  (info) max over grid[::3] of R_empty+R^m = {tot[jj]:.12f} at t/eta={grid[::3][jj]:.6f}")
    else:
        tot = np.array([obj.value(fr(g)) + obj.R_empty(fr(g)) for g in grid[::3]])
        jj = int(np.argmax(tot))
        print(f"  (info) max over grid[::3] of R_empty+R^m = {tot[jj]:.12f} at t/eta={grid[::3][jj]:.6f}")
    print(f"  time {time.time()-ts:.1f}s")
print(f"\ntotal time {time.time()-t0:.1f}s")
