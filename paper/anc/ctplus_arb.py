#!/usr/bin/env python3
r"""
ctplus_arb.py -- rigorous interval-arithmetic (Arb) upper bound for the fixed-eta Toeplitz constant

    C_T^+(w) = sup_S ess sup_{t>0} [ R_S(t) + R^m(t) ]

via Proposition prop:CTfixed of lemma-toeplitz-C.tex, for the log-wide weights
    sharp       w~(u) = h(log 1/u),  h = 1_[0,L]                 I_w = L
    lsmooth     w~(u) = h(log 1/u),  h = sin^2(pi y/L) 1_[0,L]   I_w = L/2
with eta = 1/N0, L = log N0.  All arithmetic on real numbers is done in Arb (python-flint) ball
arithmetic; every comparison that decides the result is done on exact rational endpoints (fmpq).

WHAT IS BOUNDED (notation of the lemma file; x = 1/t, X = log x, a_n^S = f_S(n)/n, EI = E*I_w):
  R_S(x)  = EI^{-1} sum_{eta x <= n <= x} a_n^S h(log(x/n)),
  R^m(x)  = EI^{-1} sum_k phi(k)/k^2 m~(k/x),   m~(u) = (sum_{mu(r)=-1} nu_r w~(ur) - w~(u))_+,  nu_r = 1/(r^2 phi(r)).
prop:CTfixed:  C_T^+ <= max_{S1 subset P0} esssup_t (R_{S1}+R^m) + (1/2) M_w delta_{P0},
  M_w = max_{S1} sup_t R_{S1}(t),  P0 = {2,3,5,7,11,13}  (64 sets S1),
  far field (a): R_S(t) <= 1 + TV(h) sup_{s>=log T1}|E_S(s)|/EI   for a.e. t < eta/T1   (TV(h) = 2),
  far field (b): R^m(t) <= EI^{-1}[(6/pi^2) I_m + (18 c_phi/pi^2) T^-2 + 2 B_phi t^{1/2} V'_m]  for t < eta/T,
                 V'_m <= 2 eta^{-1/2} (1 + sum_{mu(r)=-1} r^{1/2} nu_r) TV(h)   (as stated in the lemma).
REGIONS (NS = near-field cut-off, T1 = NS/N0, T2 = cut-off for the direct R^m bound):
  near   x <= NS         : R_S evaluated from interval prefix sums (sharp: exactly, block by block;
                           lsmooth: on a grid in X with the second-order interpolation bound
                           sup_[X_j,X_j+1] R <= max(R(X_j),R(X_j+1)) + (dX)^2/8 * sup|R''|,
                           |R''| <= EI^{-1} (2 pi^2/L^2) sum_{window} a_n  [h' is (2pi^2/L^2)-Lipschitz]);
                           R^m bounded directly (see below).
  mid    NS < x <= T2 N0 : R_S <= far bound (a) with T1 = NS/N0; R^m bounded directly.
  far    x > T2 N0       : R_S <= (a); R^m <= (b) with T = T2.
sup_{s >= log T1}|E_S(s)|, E_S(s) = F_S(s) - E (s + c_S), F_S(s) = sum_{n<=e^s} a_n^S: rigorous bracket scan over
  checkpoints in [T1, NS] (F_S and E(s+c_S) are both nondecreasing), and |E_S(s)| <= 2 B e^{-s/2} <= 2B/sqrt(NS)
  beyond NS (lem:fS(iii), B < 3.73).
R^m directly:
  sharp  : for x in the block (A N0, (A+1) N0),  E L R^m(x) <= Ut(A) := sum_{k<=A} kappa_k (G - sum_{mu(r)=-1, r<=A/k} nu_r),
           kappa_k = phi(k)/k^2, G >= sigma_0^- (because m~(u) = sum_{mu(r)=-1, ur in [eta,1]} nu_r for u < eta, 0 else).
  lsmooth: binned in Y = log(1/u) with integer bin edges ceil(exp(b delta)), exact maxima of the unimodal h on
           cells, two rigorous Arb polynomial products (arb_poly) for the two convolutions; m~ = 0 for
           Y <= L - y**, y** = (L/pi) asin(sqrt(G)) (proof in the log).
Nothing is taken from floating point: floats are used only to choose grid points and for printing.

usage:  python3 ctplus_arb.py sharp|lsmooth N0 [--NS 1000000] [--T2 1000000] [--out results]
"""
import sys, os, time, json, math, argparse, itertools
import numpy as np
from flint import arb, acb, fmpq, fmpz, arb_poly, ctx

PREC = 64
ctx.prec = PREC
P0 = [2, 3, 5, 7, 11, 13]
T00 = time.time()


def log(msg):
    print(f"[{time.time() - T00:7.1f}s] {msg}", flush=True)


# ---------------------------------------------------------------- exact endpoints
def _dy(me):
    m, e = me
    m = int(m); e = int(e)
    return fmpq(m * (1 << e)) if e >= 0 else fmpq(m, 1 << (-e))


def ub(x):
    """exact rational upper bound of the ball x"""
    assert x.is_finite(), x
    return _dy(x.upper().man_exp())


def lb(x):
    assert x.is_finite(), x
    return _dy(x.lower().man_exp())


def A(q):
    """exact rational -> ball"""
    return arb(q)


def interval(lo, hi):
    return arb(lo).union(arb(hi))


def fdec(q, d=9):
    return f"{float(q):.{d}f}"


# ---------------------------------------------------------------- sieves (exact integers)
def spf_sieve(N):
    spf = np.zeros(N + 1, np.int64)
    for p in range(2, math.isqrt(N) + 1):
        if spf[p] == 0:
            blk = spf[p * p::p]
            blk[blk == 0] = p
    idx = np.nonzero(spf == 0)[0]
    spf[idx] = idx
    spf[0] = 0
    spf[1] = 1
    return spf


def primes_upto(N):
    s = np.ones(N + 1, bool)
    s[:2] = False
    for p in range(2, math.isqrt(N) + 1):
        if s[p]:
            s[p * p::p] = False
    return np.nonzero(s)[0]


def phi_mu(N):
    P = primes_upto(N)
    phi = np.arange(N + 1, dtype=np.int64)
    mu = np.ones(N + 1, np.int8)
    for p in P.tolist():
        phi[p::p] -= phi[p::p] // p
        mu[p::p] *= -1
        if p * p <= N:
            mu[p * p::p * p] = 0
    mu[0] = 0
    return phi, mu


# ---------------------------------------------------------------- global constants (Arb)
def Ecal(Pc, pr=None):
    """E = prod_p (1 - p^-2 - p^-3): exact rational factors for p <= Pc (Arb product); tail: primes p > Pc >= 7
    are = +-1 mod 6, so prod_{p>Pc}(1-x_p) >= 1 - sum_{n>Pc, n=+-1 (6)} (n^-2 + n^-3) >= 1 - 1/(3(Pc-6)) - 1/(6(Pc-6)^2)."""
    if pr is None:
        pr = primes_upto(Pc).tolist()
    Ep = arb(1)
    for p in pr:
        p3 = p * p * p
        Ep *= A(fmpq(p3 - p - 1, p3))
    tau = A(fmpq(1, 3 * (Pc - 6))) + A(fmpq(1, 6 * (Pc - 6) ** 2))
    return Ep * interval(lb(1 - tau), fmpq(1))


def global_constants(Pc, R0, phi, mu):
    """E, c_empty, B, delta_P0 over primes <= Pc with explicit tails; G >= sigma_0^-, s_half over r <= R0 with tails."""
    pr = primes_upto(Pc).tolist()
    one = arb(1)
    c0s = arb(0); Bp = arb(1); dp = arb(1)
    for p in pr:
        p3 = p * p * p
        c0s += A(fmpq(p + 1, p3 - p - 1)) * arb(p).log()
        Bp *= one + arb(p).rsqrt() / (p - 1) + A(fmpq(1, p * p * (p - 1)))
        if p > 13:
            dp *= A(fmpq(p ** 4 - p3 + 2, p ** 4 - p3))
    P = arb(Pc)
    E = Ecal(Pc, pr)
    # c_empty tail: sum_{p>Pc} (p+1) log p/(p^3-p-1) <= 1.0001 int_Pc^oo (t^-2+t^-3) log t dt
    tauc = arb(fmpq(10001, 10000)) * ((P.log() + 1) / P + (2 * P.log() + 1) / (4 * P * P))
    c0 = arb.const_euler() + c0s + interval(fmpq(0), ub(tauc))
    # B tail: sum_{p>Pc} x_p <= (1+2/Pc) 2/sqrt(Pc) + 1/Pc^2
    tauB = (one + 2 / P) * 2 / P.sqrt() + one / (P * P)
    B = Bp * interval(fmpq(1), ub(tauB.exp()))
    # delta_P0 tail: sum_{n>Pc} 2/(n^3(n-1)) <= 2/(3 (Pc-1)^3)
    taud = arb(2) / (3 * (P - 1) ** 3)
    dP0 = dp * interval(fmpq(1), ub(taud.exp())) - 1
    # sigma_0^- and s_half over squarefree r <= R0 with mu(r) = -1; tails:
    #   sum_{r>=y} mu^2(r)/(r^2 phi(r)) <= 3/y^2  (proof of lem:Omega),
    #   sum_{r>R0} mu^2(r) r^{1/2}/(r^2 phi(r)) <= (5/3) zeta(2)zeta(3)/zeta(6) R0^{-3/2}   (see README).
    rs = np.nonzero(mu[1:R0 + 1] == -1)[0] + 1
    sig0 = arb(0); sh = arb(0)
    for r in rs.tolist():
        nr = A(fmpq(1, r * r * int(phi[r])))
        sig0 += nr
        sh += nr * arb(r).sqrt()
    z = arb(2).zeta() * arb(3).zeta() / arb(6).zeta()
    G = sig0 + interval(fmpq(0), ub(arb(3) / arb(R0 + 1) ** 2))
    s_half = sh + interval(fmpq(0), ub(arb(fmpq(5, 3)) * z / arb(R0) ** fmpq(3, 2)))
    c_phi = 12 * arb.const_glaisher().log() - (2 * arb.pi()).log()
    B_phi = arb(fmpq(3, 2)).zeta() / arb(3).zeta()
    return dict(E=E, c0=c0, B=B, dP0=dP0, G=G, s_half=s_half, c_phi=c_phi, B_phi=B_phi, rs_neg=rs)


def rho_tab(S):
    """tab[sig] = prod_{p in S} f_S(p^v)/f_empty(p^v), v = min(v_p(n),2); sig = sum_i 3^i v_i  (exact rationals)"""
    tab = []
    for s in range(3 ** len(P0)):
        x = s; val = fmpq(1)
        for p in P0:
            v = x % 3; x //= 3
            if p in S and v > 0:
                c = fmpq(p * p - p - 1, p * p)
                val *= (fmpq(p - 2, p - 1) if v == 1 else fmpq(p - 1, p)) / c
        tab.append(val)
    return tab


def fS_exact(n, S, spf):
    """exact f_S(n) (fmpq), for self-checks"""
    val = fmpq(1)
    while n > 1:
        p = int(spf[n]); a = 0
        while n % p == 0:
            n //= p; a += 1
        if p in S:
            val *= fmpq(p - 2, p - 1) if a == 1 else fmpq(p - 1, p)
        else:
            val *= fmpq(p * p - p - 1, p * p)
    return val


def geometric_ints(lo, hi, ratio):
    out = [lo]
    while out[-1] < hi:
        out.append(min(hi, max(out[-1] + 1, int(math.floor(out[-1] * ratio)))))
    return out


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('kind', choices=['sharp', 'lsmooth'])
    ap.add_argument('N0', type=int)
    ap.add_argument('--NS', type=int, default=10 ** 6)
    ap.add_argument('--T2', type=int, default=10 ** 6)
    ap.add_argument('--Pc', type=int, default=10 ** 7, help='primes <= Pc in E, c_empty, B, delta_P0')
    ap.add_argument('--R0', type=int, default=10 ** 6, help='r <= R0 in the mu(r)=-1 sums')
    ap.add_argument('--dgrid', type=int, default=1000, help='lsmooth R_S grid: mesh 1/dgrid in log x')
    ap.add_argument('--dbin', type=int, default=1000, help='lsmooth R^m bins: width 1/dbin')
    ap.add_argument('--out', default='results')
    ap.add_argument('--subsets', default='all', help="'all' or e.g. '0:8' (index range, for testing)")
    a = ap.parse_args()
    kind, N0, NS, T2 = a.kind, a.N0, a.NS, a.T2
    assert NS % N0 == 0 and T2 >= 1
    T1 = NS // N0
    sharp = (kind == 'sharp')
    os.makedirs(a.out, exist_ok=True)
    tag = f"{kind}_{N0}"
    import platform, flint
    log(f"ctplus_arb {tag}: NS={NS} T1={T1} T2={T2} Pc={a.Pc} R0={a.R0} prec={PREC} dgrid=1/{a.dgrid} dbin=1/{a.dbin}")
    log(f"environment: python {platform.python_version()}, python-flint {flint.__version__} (FLINT {flint.__FLINT_VERSION__}), "
        f"numpy {np.__version__}, {platform.machine()} {platform.system()}")

    # ---------------- sieve (exact)
    L_f = math.log(N0)
    ystar_f = (L_f / math.pi) * math.asin(math.sqrt(0.3212))
    Kmax_guess = 1 if sharp else int(math.exp(math.log(T2) + ystar_f + 0.01)) + 10
    NSV = max(NS, a.R0, T2, Kmax_guess) + 10
    phi, mu = phi_mu(NSV)
    spf = spf_sieve(NS)
    log(f"sieve to {NSV} done")

    K = global_constants(a.Pc, a.R0, phi, mu)
    E, c0, B, dP0, G, s_half, c_phi, B_phi = (K[k] for k in ('E', 'c0', 'B', 'dP0', 'G', 's_half', 'c_phi', 'B_phi'))
    log(f"E in [{fdec(lb(E), 13)}, {fdec(ub(E), 13)}]  c_empty in [{fdec(lb(c0), 10)}, {fdec(ub(c0), 10)}]  "
        f"B <= {fdec(ub(B), 6)}  delta_P0 <= {float(ub(dP0)):.6e}  sigma_0^- <= G = {fdec(ub(G), 12)}  "
        f"s_half <= {fdec(ub(s_half), 9)}  c_phi = {fdec(lb(c_phi), 9)}..  B_phi = {fdec(lb(B_phi), 9)}..  "
        f"C_G = 6/(pi^2 E) <= {fdec(ub(6 / (arb.pi() ** 2 * E)), 10)}")
    # the lemma file states B < 3.73, delta_P0 < 5.83e-5, sigma_0^- < 0.33: confirm
    assert ub(B) < fmpq(373, 100) and ub(dP0) < fmpq(583, 10 ** 7) and ub(G) < fmpq(33, 100)
    Bst = arb(fmpq(373, 100))           # the stated bound of lem:fS(iii) is used from here on
    pi = arb.pi()
    L = arb(N0).log()
    Iw = L if sharp else L / 2
    EI = E * Iw
    TVh = 2
    two_pi2_L2 = 2 * pi * pi / (L * L)
    log(f"L = {L}  I_w = {Iw}  E I_w in [{fdec(lb(EI), 12)}, {fdec(ub(EI), 12)}]")

    # ---------------- a_n^empty = f_empty(n)/n  (exact rational factors, Arb products), P0-signature
    a0 = [arb(0)] * (NS + 1)
    f0 = [arb(0)] * (NS + 1)
    f0[1] = arb(1); a0[1] = arb(1)
    cp_tab = {}
    for n in range(2, NS + 1):
        p = int(spf[n]); m = n // p
        if m % p == 0:
            f0[n] = f0[m]
        else:
            c = cp_tab.get(p)
            if c is None:
                c = cp_tab[p] = A(fmpq(p * p - p - 1, p * p))
            f0[n] = f0[m] * c
        a0[n] = f0[n] / n
    del f0
    nn = np.arange(NS + 1)
    sig = np.zeros(NS + 1, np.int64)
    for i, p in enumerate(P0):
        sig += (3 ** i) * ((nn % p == 0).astype(np.int64) + (nn % (p * p) == 0).astype(np.int64))
    sig = sig.tolist()
    log("a_n^empty and signatures done")

    omega = 2 * pi / L
    if not sharp:
        # c_n = n^{-i omega}, completely multiplicative; c_p = exp(-i omega log p) in Arb
        cc = [acb(0)] * (NS + 1)
        cc[1] = acb(1)
        cpr = {}
        for n in range(2, NS + 1):
            p = int(spf[n])
            if p == n:
                cc[n] = acb(0, -omega * arb(p).log()).exp()
            else:
                cc[n] = cc[n // p] * cc[p]
        log("c_n = n^{-i omega} done")

    subsets = [tuple(c) for k in range(len(P0) + 1) for c in itertools.combinations(P0, k)]
    if a.subsets != 'all':
        i0, i1 = map(int, a.subsets.split(':'))
        subsets = subsets[i0:i1]

    # ---------------- checkpoints
    Mint = 20000
    scan_cps = list(range(T1, max(T1, Mint) + 1)) if T1 <= Mint else [T1]
    scan_cps += geometric_ints(scan_cps[-1], NS, 1.0005)[1:]
    scan_cps = sorted(set(c for c in scan_cps if T1 <= c <= NS))
    assert scan_cps[0] == T1 and scan_cps[-1] == NS
    if sharp:
        need = set(range(0, T1 + 1)) | set((A_ + 1) * N0 - 1 for A_ in range(T1)) | set(scan_cps)
    else:
        SH = 20
        dg = 1.0 / a.dgrid
        nums = []
        j = 0
        while True:
            xv = math.exp(j * dg)
            if xv >= NS:
                break
            nums.append(int(round(xv * (1 << SH))))
            j += 1
        nums = sorted(set(nums))
        nums = [v for v in nums if v < (NS << SH)] + [NS << SH]
        assert nums[0] == (1 << SH)
        gm = [v >> SH for v in nums]                 # floor(x_j)
        gk = [v // (N0 << SH) for v in nums]         # floor(eta x_j)
        need = set(gm) | set(gk) | set(scan_cps)
    cps = sorted(c for c in need if c >= 1)
    log(f"{len(cps)} checkpoints")

    # E(log g) for the scan
    Elog = {g: E * arb(g).log() for g in scan_cps}
    esc_tail = 2 * Bst / arb(NS).sqrt()          # |E_S(s)| <= 2B e^{-s/2} for s >= log NS

    # ---------------- R^m bounds (S-independent)
    res_Rm = {}
    if sharp:
        # I_m = sum_{mu(r)=-1} nu_r min(log r, L)  (+ tail L*3/(R0+1)^2)
        Im = arb(0)
        for r in K['rs_neg'].tolist():
            nr = A(fmpq(1, r * r * int(phi[r])))
            Im += nr * (arb(r).log() if r <= N0 else L)
        Im += L * interval(fmpq(0), ub(arb(3) / arb(a.R0 + 1) ** 2))
        # Ut(A), A = 0..T2
        kap = [arb(0)] + [A(fmpq(int(phi[k]), k * k)) for k in range(1, T2 + 1)]
        D = [arb(0)] * (T2 + 1)
        for r in K['rs_neg'].tolist():
            if r > T2:
                break
            nr = A(fmpq(1, r * r * int(phi[r])))
            for k in range(1, T2 // r + 1):
                D[k * r] += kap[k] * nr
        Ut = [arb(0)] * (T2 + 1)
        acc = arb(0)
        for A_ in range(1, T2 + 1):
            acc = acc + kap[A_] * G - D[A_]
            Ut[A_] = acc
        EL = EI
        U_ub = [ub(u / EL) for u in Ut]
        del kap, D
        Rm_mid = max(U_ub[T1:T2])                  # blocks A in [T1, T2): x in (NS, T2 N0)
        log(f"sharp R^m: U(A) done; max_(A<T1) U = {fdec(max(U_ub[:T1]), 6)}, max_(T1<=A<T2) U = {fdec(Rm_mid, 6)}; "
            f"I_m <= {fdec(ub(Im), 8)}")
    else:
        dm = fmpq(1, a.dbin)
        # y** >= (L/pi) asin(sqrt(sigma_0^-)): m~(u) = 0 for Y = log(1/u) <= L - y**
        ystar = ub((L / pi) * arb(ub(G)).sqrt().asin())
        Ycut = lb(L - A(ystar))
        XT2 = arb(T2 * N0).log()
        Jtop = int(math.ceil(float(ub(XT2)) * a.dbin)) + 2          # X-cells j = 0..Jtop-1 cover [0, Jtop*dm]
        assert fmpq(Jtop) * dm > ub(XT2)
        Kmax = int(math.ceil(float(ub((A(fmpq(Jtop) * dm) - A(Ycut)).exp())))) + 1
        assert Kmax <= NSV - 5, (Kmax, NSV)
        # integer bin edges E_b = ceil(exp(b dm)): n in [E_b, E_{b+1}) => log n in [b dm, (b+1) dm)
        edges = []
        b = 0
        topN = max(Kmax, a.R0) + 1
        while True:
            v = A(dm * b).exp().ceil().unique_fmpz()
            assert v is not None
            edges.append(int(v))
            if int(v) > topN:
                break
            b += 1
        edges_np = np.array(edges, dtype=np.int64)

        def binof(n_arr):
            return np.searchsorted(edges_np, n_arr, side='right') - 1

        # r-bins of nu_r (mu(r) = -1, r <= R0)
        rs = K['rs_neg']
        rb = binof(rs)
        nub = [arb(0)] * (int(rb.max()) + 1)
        for r, bb in zip(rs.tolist(), rb.tolist()):
            nub[bb] += A(fmpq(1, r * r * int(phi[r])))
        # k-bins of kappa_k = phi(k)/k^2, k <= Kmax
        kb = binof(np.arange(1, Kmax + 1)).tolist()
        kbins = [arb(0)] * (kb[-1] + 1)
        phl = phi[:Kmax + 1].tolist()
        for k in range(1, Kmax + 1):
            kbins[kb[k - 1]] += A(fmpq(phl[k], k * k))
        log(f"lsmooth R^m: y** <= {fdec(ystar, 6)}, Ycut = {fdec(Ycut, 6)}, Kmax = {Kmax}, {len(nub)} r-bins, {len(kbins)} k-bins")

        Lhalf = L / 2

        def h_ball(y):          # y: exact fmpq or arb -> ball containing h(y)
            y = A(y) if isinstance(y, fmpq) else y
            if y < 0 or y > L:
                return arb(0)
            s = (pi * y / L).sin() ** 2
            if y >= 0 and y <= L:
                return s
            return arb(0).union(s)

        def h_max_on(lo, hi):   # exact upper bound of max_{[lo,hi]} h, lo<hi rationals
            if A(hi) <= 0 or A(lo) >= L:
                return fmpq(0)
            if A(hi) < Lhalf:
                return ub(h_ball(hi))
            if A(lo) > Lhalf:
                return ub(h_ball(lo))
            return fmpq(1)

        Dh = int(math.ceil(float(ub(L)) * a.dbin)) + 3
        hU2 = [h_max_on(dm * (d - 1), dm * (d + 1)) for d in range(Dh + 1)]      # Y - log r in ((d-1)dm, (d+1)dm]
        tailr = ub(arb(3) / arb(a.R0 + 1) ** 2)
        Imax = Jtop                                                           # Y-cells i = 0..Imax
        conv1 = arb_poly(nub) * arb_poly([A(v) for v in hU2])
        c1 = conv1.coeffs()
        Mb = [fmpq(0)] * (Imax + 1)
        for i in range(Imax + 1):
            if dm * (i + 1) <= Ycut:
                continue                                                      # proved: m~ = 0 there
            hmin = min(lb(h_ball(dm * i)), lb(h_ball(dm * (i + 1))))            # h quasi-concave: min at an endpoint
            sU = c1[i] if i < len(c1) else arb(0)
            v = ub(sU + A(tailr) - A(hmin))
            Mb[i] = v if v > 0 else fmpq(0)
        M2 = [Mb[0]] + [max(Mb[d - 1], Mb[d]) for d in range(1, Imax + 1)]
        conv2 = arb_poly(kbins) * arb_poly([A(v) for v in M2])
        c2 = conv2.coeffs()
        Rm_cell = []
        for j in range(Jtop):
            if dm * (j + 1) <= Ycut:
                Rm_cell.append(fmpq(0)); continue
            Rm_cell.append(ub(c2[j] / EI) if j < len(c2) else fmpq(0))
        Ytop = dm * (Imax + 1)
        assert A(Ytop) > L
        Im = A(dm) * A(sum(Mb, fmpq(0))) + 3 * (-(2 * (A(Ytop) - L))).exp() / 2
        jNS = int(math.floor(float(lb(arb(NS).log())) * a.dbin))
        Rm_mid = max(Rm_cell[jNS:Jtop])
        iMb = max(range(Imax + 1), key=lambda i: Mb[i])
        jR = max(range(Jtop), key=lambda j: Rm_cell[j])
        log(f"lsmooth R^m: sup m~ <= {fdec(Mb[iMb], 6)} (Y-cell {iMb}, u/eta ~ {math.exp(L_f - iMb / a.dbin):.3f}); "
            f"sup R^m <= {fdec(Rm_cell[jR], 6)} (t/eta ~ {math.exp(L_f - jR / a.dbin):.4f}); "
            f"mid-region (x in (NS,T2 N0]) sup R^m <= {fdec(Rm_mid, 6)}; I_m <= {fdec(ub(Im), 8)}")
    # far field (b) with T = T2
    Vterm = 8 * B_phi * (1 + s_half) / arb(T2).sqrt()        # 2 B_phi (eta/T2)^{1/2} * 2 eta^{-1/2}(1+s_half) TV(h)
    Rm_far = ub(((6 / (pi * pi)) * Im + (18 * c_phi / (pi * pi)) / arb(T2) ** 2 + Vterm) / EI)
    log(f"far field (b), t < eta/T2: R^m <= {fdec(Rm_far, 6)}   [(6/pi^2)I_m/EI = {fdec(ub((6/(pi*pi))*Im/EI), 6)}, "
        f"V'-term/EI = {fdec(ub(Vterm/EI), 6)}]")

    if not sharp:
        # grid data
        Xg = [A(fmpq(v, 1 << SH)).log() for v in nums]
        Eph = [acb(0, omega * X).exp() for X in Xg]
        dX_ub = [ub(Xg[j + 1] - Xg[j]) for j in range(len(nums) - 1)]
        assert max(dX_ub) < fmpq(11, 10 * a.dgrid)
        Kpp = two_pi2_L2 / EI / 8
        # R^m over each grid cell: max over the R^m X-cells meeting [X_j, X_{j+1}]
        Rm_grid = []
        for j in range(len(nums) - 1):
            j0 = int(math.floor(float(lb(Xg[j])) * a.dbin)) - 1
            j1 = int(math.floor(float(ub(Xg[j + 1])) * a.dbin)) + 1
            Rm_grid.append(max(Rm_cell[max(j0, 0):min(j1, Jtop - 1) + 1]))

    # ---------------- per-S pass
    results = []
    tS = time.time()
    for S in subsets:
        tab = [A(q) for q in rho_tab(S)]
        s0 = arb(0)
        P0d = {0: arb(0)}
        if sharp:
            n = 1
            for cp in cps:
                for m in range(n, cp + 1):
                    s0 += a0[m] * tab[sig[m]]
                P0d[cp] = s0
                n = cp + 1
        else:
            s1 = acb(0)
            P1d = {0: acb(0)}
            n = 1
            for cp in cps:
                for m in range(n, cp + 1):
                    am = a0[m] * tab[sig[m]]
                    s0 += am
                    s1 += am * cc[m]
                P0d[cp] = s0; P1d[cp] = s1
                n = cp + 1
        # c_S and the E_S scan
        cS = c0 - sum((arb(p).log() / A(fmpq(p ** 3 * (p - 1)) * fmpq(p ** 3 - p - 1, p ** 3)) for p in S), arb(0))
        EcS = E * cS
        esc = fmpq(0)
        for g0, g1 in zip(scan_cps[:-1], scan_cps[1:]):
            Flo = P0d[g0]
            Fhi = P0d[g0] if g1 == g0 + 1 else P0d[g1]
            v = max(ub(Fhi - (Elog[g0] + EcS)), ub((Elog[g1] + EcS) - Flo))
            if v > esc:
                esc = v
        esup = max(esc, ub(esc_tail))
        farS = ub(1 + TVh * A(esup) / EI)
        r = dict(S=list(S), esc_scan=str(esc), esup=str(esup), farS=str(farS))
        if sharp:
            EL = EI
            best = fmpq(-1); bestA = -1; bestR = fmpq(-1); bestRA = -1; lowR = fmpq(-1)
            for A_ in range(T1):
                vv = P0d[(A_ + 1) * N0 - 1] - P0d[A_]
                R = vv / EL
                uR = ub(R)
                tot = uR + U_ub[A_]
                if tot > best:
                    best, bestA = tot, A_
                if uR > bestR:
                    bestR, bestRA = uR, A_
                lR = lb(R)
                if lR > lowR:
                    lowR = lR
            near = best
            nearRS = bestR
            # region t < eta (x > N0, blocks A >= 1), where mu^- and R^m live (sharp weight)
            mureg = max((ub((P0d[(A_ + 1) * N0 - 1] - P0d[A_]) / EL) + U_ub[A_] for A_ in range(1, T1)), default=fmpq(0))
            MwS = max(nearRS, farS) + ub(arb(1) / (N0 * EL))      # pointwise-sup correction (see README)
            r.update(near=str(near), near_A=bestA, nearRS=str(nearRS), nearRS_A=bestRA, nearRS_lower=str(lowR))
            # self-check: exact rational F(N0-1) for this S is inside the ball
            if S in [(), (2,), (13,), (2, 3, 5, 7, 11, 13)]:
                ex = sum((fS_exact(k, S, spf) / k for k in range(1, N0)), fmpq(0))
                assert lb(P0d[N0 - 1]) <= ex <= ub(P0d[N0 - 1]), "self-check failed"
                r['selfcheck'] = 'F(N0-1) exact rational inside ball: OK'
        else:
            half = arb(fmpq(1, 2))
            Rg = []
            for j in range(len(nums)):
                m_, k_ = gm[j], gk[j]
                W0 = P0d[m_] - P0d[k_]
                W1 = P1d[m_] - P1d[k_]
                Rg.append(half * (W0 - (Eph[j] * W1).real) / EI)
            Rub = [ub(x) for x in Rg]
            best = fmpq(-1); bestj = -1; bestR = fmpq(-1); bestRj = -1
            for j in range(len(nums) - 1):
                err = ub(A(dX_ub[j]) ** 2 * Kpp * P0d[gm[j + 1]])
                cellR = max(Rub[j], Rub[j + 1]) + err
                tot = cellR + Rm_grid[j]
                if tot > best:
                    best, bestj = tot, j
                if cellR > bestR:
                    bestR, bestRj = cellR, j
            lows = [lb(x) for x in Rg]
            jl = max(range(len(nums)), key=lambda j: lows[j])
            near = best; nearRS = bestR
            # region t < 3 eta (X > L - log 3), where most of mu^- and all of R^m live (log-smooth weight)
            Xcut = lb(L - arb(3).log())
            mureg = fmpq(0)
            for j in range(len(nums) - 1):
                if ub(Xg[j + 1]) > Xcut:
                    err = ub(A(dX_ub[j]) ** 2 * Kpp * P0d[gm[j + 1]])
                    mureg = max(mureg, max(Rub[j], Rub[j + 1]) + err + Rm_grid[j])
            MwS = max(nearRS, farS)
            r.update(near=str(near), near_t_over_eta=N0 * (1 << SH) / nums[bestj], nearRS=str(nearRS),
                     nearRS_t_over_eta=N0 * (1 << SH) / nums[bestRj], nearRS_lower=str(lows[jl]),
                     nearRS_lower_t_over_eta=N0 * (1 << SH) / nums[jl])
            # self-check: direct Arb evaluation of R_S at the best grid point (no prefix sums, no cos-decomposition)
            if S in [(), (13,), (2,)]:
                X = Xg[jl]
                tot_d = arb(0)
                for k in range(gk[jl] + 1, gm[jl] + 1):
                    y = X - arb(k).log()
                    tot_d += a0[k] * tab[sig[k]] * h_ball(y)
                Rd = tot_d / EI
                assert Rd.overlaps(Rg[jl]), (Rd, Rg[jl])
                r['selfcheck'] = f'direct sum at t/eta={N0 * (1 << SH) / nums[jl]:.4f}: {Rd} vs prefix/cos {Rg[jl]}: overlap OK'
        mid = farS + Rm_mid
        far = farS + Rm_far
        total = max(near, mid, far)
        mureg = max(mureg, mid, far)
        r['mu_region'] = str(mureg)
        r.update(mid=str(mid), far=str(far), total=str(total), Mw=str(MwS),
                 where=('near' if total == near else ('mid' if total == mid else 'far')))
        results.append(r)
        if 'selfcheck' in r:
            log(f"   self-check S={list(S)}: {r['selfcheck']}")
        log(f"S={list(S)}: sup_near(R_S+R^m) <= {fdec(near, 7)} | sup_near R_S in [{fdec(fmpq(r['nearRS_lower']), 7)}, "
            f"{fdec(nearRS, 7)}] | sup|E_S| <= {float(esup):.3e} far R_S <= {fdec(farS, 6)} | mid <= {fdec(mid, 6)} far <= {fdec(far, 6)} "
            f"| total <= {fdec(total, 7)} [{r['where']}]  ({time.time() - tS:.0f}s)")

    Mw = max(fmpq(r['Mw']) for r in results)
    slack = ub(A(Mw) * dP0 / 2)
    tot = max(fmpq(r['total']) for r in results)
    Cbar = tot + slack
    rbest = max(results, key=lambda r: fmpq(r['total']))
    rlow = max(results, key=lambda r: fmpq(r['nearRS_lower']))
    r0 = next((r for r in results if r['S'] == []), None)      # S1 = empty set: sup_t R_empty <= max(near, far)
    summary = dict(kind=kind, N0=N0, NS=NS, T1=T1, T2=T2, Pc=a.Pc, R0=a.R0, prec=PREC, dgrid=a.dgrid, dbin=a.dbin,
                   n_subsets=len(results), E_lo=str(lb(E)), E_hi=str(ub(E)), B_ub=str(ub(B)), dP0_ub=str(ub(dP0)),
                   G_ub=str(ub(G)), Rm_mid=str(Rm_mid), Rm_far=str(Rm_far), Im_ub=str(ub(Im)),
                   max_total=str(tot), argmax_S=rbest['S'], Mw=str(Mw), slack=str(slack), Cbar=str(Cbar),
                   Cbar_float_up=math.ceil(float(Cbar) * 1e9) / 1e9,
                   supRS_lower=str(max(fmpq(r['nearRS_lower']) for r in results)), supRS_lower_S=rlow['S'],
                   supRS_empty_upper=(str(max(fmpq(r0['nearRS']), fmpq(r0['farS']))) if r0 else None),
                   mu_region_max=str(max(fmpq(r['mu_region']) for r in results)),
                   mu_region_def=('t < eta' if sharp else 't < 3 eta'),
                   seconds=round(time.time() - T00, 1), results=results)
    with open(os.path.join(a.out, f"ctplus_arb_{tag}.json"), 'w') as fh:
        json.dump(summary, fh, indent=1)
    log(f"SUMMARY {tag}: max_(S1) sup(R_S1+R^m) <= {fdec(tot, 9)} (S1={rbest['S']}, {rbest['where']}); "
        f"M_w <= {fdec(Mw, 7)}; slack (1/2)M_w delta_P0 <= {float(slack):.4e}; "
        f"CERTIFIED  C_T^+ <= {fdec(Cbar, 9)}   (certified lower bound for sup_(S1,t) R_S1: {fdec(fmpq(summary['supRS_lower']), 7)}); "
        f"max_(S1) sup (R_S1+R^m) over {summary['mu_region_def']} (mu^- region) <= {fdec(fmpq(summary['mu_region_max']), 6)}")
    import resource
    log(f"total time {time.time() - T00:.0f}s, peak memory {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024:.0f} MB")


if __name__ == '__main__':
    main()
