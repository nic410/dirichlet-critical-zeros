"""Task 2 (log-smooth weight).  h(y) = sin^2(pi y/L) on [0,L], I_w = L/2, X = log x, theta = 2 pi/L.
R_S(X) = (E L/2)^{-1} sum_{x/N0<=n<=x} f(n)/n sin^2(pi (X - log n)/L)
       = (E L)^{-1} [S0 - Sc cos(theta X) - Ss sin(theta X)],   on each piece x in [m, m+1]
with window n in [m//N0 + 1, m] and S0 = sum f/n, Sc = sum f/n cos(theta log n), Ss = sum f/n sin(theta log n).
(a) double precision: closed-form max on every piece m < 1e5 (exact sup over x <= 1e5 up to rounding);
(b) double-precision scan with spacing 1e-4 in X over [0, log 1e5] -> local maxima list (competitor check);
(c) mp.dps=40: closed-form max on top pieces (direct high-precision window sums);
(d) mp.dps=40: independent golden-section maximisation of the direct sin^2 sum (no expansion) in X.
"""
import time
from multiprocessing import Pool
import numpy as np
import mpmath as mp
from xcheck_common import all_subsets, label, spf_sieve, factor, f_rational, compute_E, f_over_n_float_array

N = 10**5
N0S = (100, 1000, 10000)
DPS = 40
mp.mp.dps = DPS
E_mp, _ = compute_E(dps=50, verbose=False)
E_mp = +E_mp
E_f = float(E_mp)
spf = spf_sieve(N)
FAC = [None, []] + [factor(n, spf) for n in range(2, N + 1)]
logn = np.zeros(N + 1); logn[1:] = np.log(np.arange(1, N + 1))


def piece_closed_form_double(v, N0):
    L = np.log(N0); th = 2 * np.pi / L
    c = np.cos(th * logn); s = np.sin(th * logn)
    P0 = np.cumsum(v); Pc = np.cumsum(v * c); Ps = np.cumsum(v * s)
    m = np.arange(1, N)
    A = m // N0
    S0 = P0[m] - P0[A]; Sc = Pc[m] - Pc[A]; Ss = Ps[m] - Ps[A]
    Xa = np.log(m); Xb = np.log(m + 1.0)
    B = lambda X: S0 - Sc * np.cos(th * X) - Ss * np.sin(th * X)
    rho = np.hypot(Sc, Ss); psi = np.arctan2(Ss, Sc)
    k = np.ceil((th * Xa - psi - np.pi) / (2 * np.pi))
    Xs = (psi + np.pi + 2 * np.pi * k) / th
    inside = Xs <= Xb
    val = np.maximum(B(Xa), B(Xb))
    Xbest = np.where(B(Xa) >= B(Xb), Xa, Xb)
    val = np.where(inside, S0 + rho, val)
    Xbest = np.where(inside, Xs, Xbest)
    return val / (E_f * L), Xbest


def scan_double(v, N0, step=1e-4):
    L = np.log(N0); th = 2 * np.pi / L
    c = np.cos(th * logn); s = np.sin(th * logn)
    P0 = np.cumsum(v); Pc = np.cumsum(v * c); Ps = np.cumsum(v * s)
    X = np.arange(0.0, np.log(N) + 1e-12, step)
    x = np.exp(X)
    hi = np.minimum(np.floor(x).astype(np.int64), N)
    lo = np.maximum(np.ceil(x / N0).astype(np.int64), 1)
    S0 = P0[hi] - P0[lo - 1]; Sc = Pc[hi] - Pc[lo - 1]; Ss = Ps[hi] - Ps[lo - 1]
    R = (S0 - Sc * np.cos(th * X) - Ss * np.sin(th * X)) / (E_f * L)
    # local maxima
    lm = np.nonzero((R[1:-1] > R[:-2]) & (R[1:-1] >= R[2:]))[0] + 1
    return X, R, lm


def fn_mp(S, n):
    num, den = f_rational(FAC[n], S)
    return mp.mpf(num) / (den * n)


def hp_piece(S, N0, m, cache):
    """high-precision closed-form sup on piece x in [m, m+1]."""
    L = mp.log(N0); th = 2 * mp.pi / L
    A = m // N0
    S0 = Sc = Ss = mp.mpf(0)
    for n in range(A + 1, m + 1):
        a = fn_mp(S, n)
        ln = cache.get(n)
        if ln is None:
            lg = mp.log(n); ln = (mp.cos(th * lg), mp.sin(th * lg)); cache[n] = ln
        S0 += a; Sc += a * ln[0]; Ss += a * ln[1]
    Xa, Xb = mp.log(m), mp.log(m + 1)
    B = lambda X: S0 - Sc * mp.cos(th * X) - Ss * mp.sin(th * X)
    rho = mp.sqrt(Sc ** 2 + Ss ** 2); psi = mp.atan2(Ss, Sc)
    k = mp.ceil((th * Xa - psi - mp.pi) / (2 * mp.pi))
    Xs = (psi + mp.pi + 2 * mp.pi * k) / th
    if Xs <= Xb:
        return (S0 + rho) / (E_mp * L), Xs, True
    ba, bb = B(Xa), B(Xb)
    return (max(ba, bb)) / (E_mp * L), (Xa if ba >= bb else Xb), False


def R_direct_mp(S, N0, X, fcache):
    L = mp.log(N0)
    x = mp.exp(X)
    lo = int(mp.ceil(x / N0)); hi = int(mp.floor(x))
    tot = mp.mpf(0)
    for n in range(max(lo, 1), hi + 1):
        a = fcache.get(n)
        if a is None:
            a = (fn_mp(S, n), mp.log(n)); fcache[n] = a
        tot += a[0] * mp.sin(mp.pi * (X - a[1]) / L) ** 2
    return tot / (E_mp * L / 2)


def golden(fun, a, b, tol):
    g = (mp.sqrt(5) - 1) / 2
    c = b - g * (b - a); d = a + g * (b - a)
    fc, fd = fun(c), fun(d)
    while b - a > tol:
        if fc > fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a); fc = fun(c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a); fd = fun(d)
    X = (a + b) / 2
    return fun(X), X


def work(args):
    S, do_golden = args
    mp.mp.dps = DPS
    v = f_over_n_float_array(N, S)
    out = {}
    for N0 in N0S:
        val, Xb = piece_closed_form_double(v, N0)
        order = np.argsort(-val)
        mbest = int(order[0]) + 1
        # scan
        X, R, lm = scan_double(v, N0)
        g = int(np.argmax(R))
        far = [i for i in lm if abs(X[i] - X[g]) > 0.05]
        comp = max(far, key=lambda i: R[i]) if far else None
        # high precision on top pieces +- neighbours
        cache = {}
        cands = sorted(set([mbest - 1, mbest, mbest + 1] + [int(order[j]) + 1 for j in range(3)]))
        cands = [m for m in cands if 1 <= m < N]
        hp = [(hp_piece(S, N0, m, cache), m) for m in cands]
        (hv, hX, interior), hm = max(hp, key=lambda z: z[0][0])
        rec = dict(dbl_val=float(val[order[0]]), dbl_X=float(Xb[order[0]]), dbl_m=mbest,
                   scan_val=float(R[g]), scan_X=float(X[g]),
                   comp_val=(float(R[comp]) if comp is not None else None), comp_X=(float(X[comp]) if comp is not None else None),
                   n_localmax=len(lm), hp_val=hv, hp_X=hX, hp_m=hm, hp_interior=interior)
        if do_golden:
            fc = {}
            gv, gX = golden(lambda Z: R_direct_mp(S, N0, Z, fc), mp.mpf(X[g]) - 3e-4, mp.mpf(X[g]) + 3e-4, mp.mpf(10) ** (-22))
            rec.update(gold_val=gv, gold_X=gX)
        out[N0] = rec
    return S, out


if __name__ == "__main__":
    t0 = time.time()
    subsets = all_subsets()
    named = [frozenset(), frozenset({13}), frozenset({11}), frozenset({11, 13}), frozenset({7}), frozenset({2})]
    # golden-section check for named subsets (plus the overall max, added after pass 1)
    with Pool(6) as pool:
        res = dict(pool.map(work, [(S, S in named) for S in subsets]))
    t1 = time.time()
    extra = set()
    for N0 in N0S:
        Smax = max(subsets, key=lambda S: res[S][N0]['hp_val'])
        if Smax not in named:
            extra.add(Smax)
    if extra:
        with Pool(6) as pool:
            for S, o in pool.map(work, [(S, True) for S in extra]):
                res[S] = o
    print(f"# log-smooth weight; mp.dps={DPS}; E={mp.nstr(E_mp, 25)}; pass1 {t1-t0:.1f}s total {time.time()-t0:.1f}s")
    for N0 in N0S:
        print(f"\n== log-smooth, N0={N0} ==")
        rank = sorted(subsets, key=lambda S: -res[S][N0]['hp_val'])
        for S in rank[:5]:
            r = res[S][N0]
            print(f"  top: S1={label(S):14s} sup R = {mp.nstr(r['hp_val'], 20)} at t/eta = {mp.nstr(N0 * mp.exp(-r['hp_X']), 12)} (x={mp.nstr(mp.exp(r['hp_X']), 12)}, piece m={r['hp_m']}, interior={r['hp_interior']})")
        print(f"  min over S1: {label(rank[-1])} {mp.nstr(res[rank[-1]][N0]['hp_val'], 15)}")
        for S in named + [S for S in extra if S not in named]:
            r = res[S][N0]
            line = (f"  named S1={label(S):10s} closed-form(mp{DPS}) sup R = {mp.nstr(r['hp_val'], 20)} at t/eta = {mp.nstr(N0 * mp.exp(-r['hp_X']), 12)};"
                    f" double closed-form {r['dbl_val']:.15f}; scan {r['scan_val']:.12f} @ t/eta={N0*np.exp(-r['scan_X']):.5f}")
            if 'gold_val' in r:
                line += f"\n      golden-section direct sum (mp{DPS}): {mp.nstr(r['gold_val'], 20)} at t/eta = {mp.nstr(N0 * mp.exp(-r['gold_X']), 12)};  |diff| = {mp.nstr(abs(r['gold_val'] - r['hp_val']), 3)}"
            line += f"\n      #scan local maxima={r['n_localmax']}; best competing local max (|dX|>0.05): {r['comp_val']} at t/eta={N0*np.exp(-r['comp_X']) if r['comp_X'] is not None else None}"
            print(line)
        worst_gap = min((res[S][N0]['scan_val'] - res[S][N0]['comp_val'], label(S)) for S in subsets if res[S][N0]['comp_val'] is not None)
        print(f"  competitor check over all 64 S1: min (global - best far local max) = {worst_gap[0]:.6f} ({worst_gap[1]})")
        agree = max(abs(res[S][N0]['dbl_val'] - float(res[S][N0]['hp_val'])) for S in subsets)
        print(f"  max |double closed form - mp closed form| over 64 S1 = {agree:.2e}; scan-vs-closed max diff = {max(float(res[S][N0]['hp_val']) - res[S][N0]['scan_val'] for S in subsets):.2e}")
        print("  all 64 (S1: sup R, t/eta):")
        for S in subsets:
            r = res[S][N0]
            print(f"    {label(S):18s} {mp.nstr(r['hp_val'], 16):>20s} t/eta={mp.nstr(N0 * mp.exp(-r['hp_X']), 10)}")
    print(f"\ntotal time {time.time()-t0:.1f}s")
