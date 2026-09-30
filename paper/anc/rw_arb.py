#!/usr/bin/env python3
r"""
rw_arb.py -- rigorous interval-arithmetic (Arb) upper bound for the Gauss-transfer Farey constant

    R_w = ess sup_{t>0} P_w(t),   P_w(t) = c_w^{-1} sum_{k>=1} phi(k)/k^2 w~(kt),   c_w = (6/pi^2) I_w
    (eqA:Pw, eqA:Rw of lemma-A.tex), for the log-smooth weight  w~(u) = sin^2(pi log(1/u)/L) 1_[eta,1](u),
    I_w = L/2, eta = 1/N0, L = log N0.  These are the numerical inputs of Theorem thm:fixed(iii).

near  x = 1/t <= NS : grid in X = log x (mesh 1/dgrid) with the second-order interpolation bound, exactly as in
                      ctplus_arb.py with a_k = phi(k)/k^2 in place of f_S(k)/k:
                        P_w(x) = c_w^{-1} (1/2) [ W0(x) - Re( x^{i omega} W1(x) ) ],  omega = 2 pi/L,
                        W0 = sum_{eta x < k <= x} a_k,  W1 = sum_{eta x < k <= x} a_k k^{-i omega},
                        sup_[X_j,X_j+1] P_w <= max(P_w(X_j), P_w(X_j+1)) + (dX)^2/8 c_w^{-1} (2 pi^2/L^2) sum_{k<=x_j+1} a_k.
far   x > NS         : P_w(t) <= 1 + 2 sup_{y >= T1} |E_phi(y)| / c_w,  T1 = NS/N0,
                      E_phi(y) = sum_{k<=y} phi(k)/k^2 - (6/pi^2)(log y + c_phi)  (lem:harm).
                      Proof: the proof of lem:Rwlog writes c_w P_w(t) = int_0^1 sum_{alpha_l < k < beta_l} phi(k)/k^2 dl
                      with intervals (alpha_l, beta_l), beta_l/alpha_l = e^{|{h > l}|}; for t < eta/T1 all alpha_l >
                      T1, so each inner sum is <= (6/pi^2) log(beta_l/alpha_l) + 2 sup_{y >= T1}|E_phi(y)|, and
                      int_0^1 log(beta_l/alpha_l) dl = int h = I_w.
                      sup over [T1, NS]: bracket scan on checkpoints (both terms nondecreasing); beyond NS
                      |E_phi(y)| <= 2 B_phi y^{-1/2} (lem:harm), B_phi = zeta(3/2)/zeta(3).
Also prints C_G R_w <= (6/(pi^2 E)) Rbar with a rigorous E (as in ctplus_arb.py).

usage:  python3 rw_arb.py N0 [--NS 10000000] [--out DIR]
"""
import os, sys, time, json, math, argparse, platform
import numpy as np
import flint
from flint import arb, acb, fmpq, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ctplus_arb import ub, lb, A, interval, fdec, phi_mu, primes_upto, geometric_ints, Ecal, PREC

ctx.prec = PREC
T00 = time.time()


def log(msg):
    print(f"[{time.time() - T00:7.1f}s] {msg}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('N0', type=int)
    ap.add_argument('--NS', type=int, default=10 ** 7)
    ap.add_argument('--Pc', type=int, default=10 ** 7)
    ap.add_argument('--dgrid', type=int, default=1000)
    ap.add_argument('--out', default='.')
    a = ap.parse_args()
    N0, NS = a.N0, a.NS
    assert NS % N0 == 0
    T1 = NS // N0
    tag = f"lsmooth_{N0}"
    log(f"rw_arb {tag}: NS={NS} T1={T1} Pc={a.Pc} prec={PREC} dgrid=1/{a.dgrid}")
    log(f"environment: python {platform.python_version()}, python-flint {flint.__version__} (FLINT {flint.__FLINT_VERSION__}), "
        f"numpy {np.__version__}, {platform.machine()} {platform.system()}")
    phi, _ = phi_mu(NS)
    phl = phi.tolist()
    pi = arb.pi()
    L = arb(N0).log()
    Iw = L / 2
    six = 6 / (pi * pi)
    cw = six * Iw
    omega = 2 * pi / L
    c_phi = 12 * arb.const_glaisher().log() - (2 * pi).log()
    B_phi = arb(fmpq(3, 2)).zeta() / arb(3).zeta()
    E = Ecal(a.Pc)
    log(f"c_w = (6/pi^2) L/2 in [{fdec(lb(cw), 12)}, {fdec(ub(cw), 12)}]; c_phi = {c_phi}; B_phi = {B_phi}; "
        f"E in [{fdec(lb(E), 13)}, {fdec(ub(E), 13)}]")

    # grid x_j (dyadic), checkpoints
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
    nums = sorted(set(v for v in nums if v < (NS << SH))) + [NS << SH]
    assert nums[0] == (1 << SH)
    gm = [v >> SH for v in nums]
    gk = [v // (N0 << SH) for v in nums]
    Mint = 20000
    scan = list(range(T1, max(T1, Mint) + 1)) if T1 <= Mint else [T1]
    scan += geometric_ints(scan[-1], NS, 1.0005)[1:]
    scan = sorted(set(c for c in scan if T1 <= c <= NS))
    assert scan[0] == T1 and scan[-1] == NS
    cps = sorted(c for c in (set(gm) | set(gk) | set(scan)) if c >= 1)
    log(f"{len(nums)} grid points, {len(cps)} checkpoints")

    # single pass: prefix sums of a_k and a_k k^{-i omega}
    s0 = arb(0); s1 = acb(0)
    P0d = {0: arb(0)}; P1d = {0: acb(0)}
    n = 1
    for cp in cps:
        for k in range(n, cp + 1):
            ak = A(fmpq(phl[k], k * k))
            s0 += ak
            s1 += ak * acb(0, -omega * arb(k).log()).exp()
        P0d[cp] = s0; P1d[cp] = s1
        n = cp + 1
    log("prefix sums done")

    # far field
    esc = fmpq(0)
    lin = {g: six * (arb(g).log() + c_phi) for g in scan}
    for g0, g1 in zip(scan[:-1], scan[1:]):
        Flo = P0d[g0]
        Fhi = P0d[g0] if g1 == g0 + 1 else P0d[g1]
        v = max(ub(Fhi - lin[g0]), ub(lin[g1] - Flo))
        if v > esc:
            esc = v
    esup = max(esc, ub(2 * B_phi / arb(NS).sqrt()))
    far = ub(1 + 2 * A(esup) / cw)
    log(f"sup_(y>=T1)|E_phi(y)| <= {float(esup):.4e} (scan {float(esc):.4e}, tail {float(ub(2 * B_phi / arb(NS).sqrt())):.4e}); "
        f"far field x > NS: P_w <= {fdec(far, 7)}")

    # near: grid values and cells
    half = arb(fmpq(1, 2))
    Pg = []
    for j in range(len(nums)):
        X = A(fmpq(nums[j], 1 << SH)).log()
        W0 = P0d[gm[j]] - P0d[gk[j]]
        W1 = P1d[gm[j]] - P1d[gk[j]]
        Pg.append((X, half * (W0 - (acb(0, omega * X).exp() * W1).real) / cw))
    Kpp = 2 * pi * pi / (L * L) / cw / 8
    best = fmpq(-1); bestj = -1
    for j in range(len(nums) - 1):
        dX = ub(Pg[j + 1][0] - Pg[j][0])
        assert dX < fmpq(11, 10 * a.dgrid)
        cell = max(ub(Pg[j][1]), ub(Pg[j + 1][1])) + ub(A(dX) ** 2 * Kpp * P0d[gm[j + 1]])
        if cell > best:
            best, bestj = cell, j
    lows = [lb(p[1]) for p in Pg]
    jl = max(range(len(nums)), key=lambda j: lows[j])
    # self-check: direct evaluation at the best grid point (no prefix sums, no cos-decomposition)
    X = Pg[jl][0]
    tot = arb(0)
    for k in range(gk[jl] + 1, gm[jl] + 1):
        y = X - arb(k).log()
        tot += A(fmpq(phl[k], k * k)) * (pi * y / L).sin() ** 2
    assert (tot / cw).overlaps(Pg[jl][1])
    log(f"self-check: direct sum at t/eta={N0 * (1 << SH) / nums[jl]:.4f}: {tot / cw} vs prefix/cos {Pg[jl][1]}: overlap OK")
    Rbar = max(best, far)
    CG = 6 / (pi * pi * E)
    CGR = ub(CG * A(Rbar))
    log(f"near: sup P_w <= {fdec(best, 9)} (cell at t/eta ~ {N0 * (1 << SH) / nums[bestj]:.4f}); certified lower bound "
        f"P_w(t/eta={N0 * (1 << SH) / nums[jl]:.4f}) >= {fdec(lows[jl], 9)}")
    assert ub(CG) < fmpq(1268774, 10 ** 6)          # the text uses C_G < 1.268774
    log(f"SUMMARY {tag}: CERTIFIED  R_w <= {fdec(Rbar, 9)}   (ess sup R_w >= {fdec(lows[jl], 7)});  "
        f"C_G <= {fdec(ub(CG), 10)} < 1.268774;  C_w = C_G R_w <= {fdec(CGR, 9)}")
    out = dict(kind='lsmooth', N0=N0, NS=NS, T1=T1, Rbar=str(Rbar), R_lower=str(lows[jl]), far=str(far), esup=str(esup),
               CG_ub=str(ub(CG)), CGR_ub=str(CGR), seconds=round(time.time() - T00, 1))
    with open(os.path.join(a.out, f"rw_arb_{tag}.json"), 'w') as fh:
        json.dump(out, fh, indent=1)
    import resource
    log(f"total time {time.time() - T00:.0f}s, peak memory {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024:.0f} MB")


if __name__ == '__main__':
    main()
