"""Computer-assisted upper bound for C_T^+(w) = sup_S ess sup_t [R_S(t) + R^m(t)]  (A = q/phi family).

  R_S(t)  = (E I_w)^{-1} sum_n f_S(n)/n * Wt(n t),      Wt(u) = u^2 w(u) = h(log 1/u)
  R^m(t)  = (E I_w)^{-1} sum_k phi(k)/k^2 * mt(k t),    mt(u) = ( sum_{mu(r)=-1} Wt(ur)/(r^2 phi(r)) - Wt(u) )^+
  x := 1/t,  N0 := 1/eta,  L := log N0.

Reduction over S: C_T^+ <= max_{S1 subset P0} ess sup_t [R_{S1}+R^m] + M(prod_{p>13}(1+2/(p^3(p-1)))-1)/2.

Regions:
  near   x <= NS          : R_S exact (sharp: exact step-function ess sup; lsmooth: binned upper bound, bin error
                            (pi/L)*delta*mass, rigorous for every X in each cell), R^m exact bound (sharp: U(A); lsmooth: binned)
  middle NS < x <= T2*N0  : R_S <= 1 + 2 sup_{s>=log(NS/N0)} |E_S(s)| / (E I_w)   (exact identity, Y > L);  R^m as above
  far    x > T2*N0        : R_S as middle; R^m <= (E I_w)^{-1}[(6/pi^2) I_m + (6/pi^2) c_phi 2.916/T2^2 + 2 B_phi T2^{-1/2} eta^{1/2} V_m]
|E_S(s)| numerically for e^s in [NS/N0, NS], and <= 2 B_S(1/2) e^{-s/2} beyond NS (proved bound).
Floating point throughout (float64); no interval arithmetic.
usage: python3 ctplus.py sharp|lsmooth N0 NS T2 [delta]
"""
import sys, math, time, itertools
import numpy as np
from scipy.signal import fftconvolve
from arith_lib import (spf_sieve, primes_from_spf, phi_mu, f_empty, signature, factor_table, P0,
                       E_and_c, cS_of, B_half, GAMMA)

t00 = time.time()
kind = sys.argv[1]; N0 = int(sys.argv[2]); NS = int(sys.argv[3]); T2 = int(sys.argv[4])
delta = float(sys.argv[5]) if len(sys.argv) > 5 else 2e-5
L = math.log(N0)
Iw = L if kind == 'sharp' else L/2
E_lo, E_hi, c0, c0_tail = E_and_c(10**7)
EI = E_lo*Iw                      # lower bound for E*I_w  => upper bounds for R
RMAX = 10**7                      # r-sums truncated at RMAX, tail sum_{r>=y} mu^2/(r^2 phi) <= 2.916/y^2
TAILR = 2.916/RMAX**2
T1 = NS // N0
B_phi = 2.6123753486854883/1.2020569031595942    # zeta(3/2)/zeta(3)
c_phi = GAMMA + 0.5699610427687271                 # gamma - zeta'(2)/zeta(2), zeta'(2)/zeta(2) = -0.56996...
PROD = 5.82423056014747e-05 * 1.0001               # prod_{p>13}(1+2/(p^3(p-1))) - 1 (computed to 1e7; tail negligible), padded
print(f"# kind={kind} eta=1/{N0} L={L:.6f} I_w={Iw:.6f} E in [{E_lo:.12f},{E_hi:.12f}] c_empty={c0:.10f}(+{c0_tail:.1e}) "
      f"NS={NS} T1=NS/N0={T1} T2={T2} delta={delta}", flush=True)

# ---- sieves
NMAX = max(NS, RMAX)
if kind == 'lsmooth':
    Gguess = 0.33
    ystar = (L/math.pi)*math.asin(math.sqrt(Gguess))
    Kneed = int(math.exp(math.log(T2*N0) - (L - ystar) + 3*delta)) + 2
    NMAX = max(NMAX, Kneed)
spf = spf_sieve(NMAX); P = primes_from_spf(spf)
phi, mu = phi_mu(NMAX, P)
print(f"# sieve to {NMAX} done {time.time()-t00:.1f}s", flush=True)
r_all = np.arange(NMAX + 1)
negr = np.nonzero(mu[:RMAX + 1] == -1)[0]
nu = 1.0/(negr.astype(np.float64)**2*phi[negr])
G_inf = float(nu.sum()) + TAILR
assert G_inf < 1
print(f"# G_inf = sum_{{mu(r)=-1}} 1/(r^2 phi(r)) <= {G_inf:.12f}", flush=True)

f0 = f_empty(NS, P[P <= NS])
sig = signature(NS)
nn = np.arange(NS + 1, dtype=np.float64); nn[0] = 1.0
subsets = [list(c) for k in range(len(P0) + 1) for c in itertools.combinations(P0, k)]

# ---- E_S sup helper
def Esup(F, cS, lo, hi):
    n = np.arange(lo, hi, dtype=np.float64)
    Fn = F[lo:hi]
    e1 = np.abs(Fn - E_hi*(np.log(n) + cS)); e2 = np.abs(Fn - E_hi*(np.log(n + 1) + cS))
    return float(max(e1.max(), e2.max()))
# numerical slack for E, c_S uncertainty: |dE|*(s+c) + E*dc  (s <= 17)
ESLACK = (E_hi - E_lo)*20 + E_hi*(c0_tail + 1e-12) + 1e-9

results = []
if kind == 'sharp':
    # ---- U(A) for A <= T2 :  sup of R^m over block x in (A N0,(A+1)N0)  times E L
    A_ = np.arange(T2 + 1, dtype=np.float64)
    D = np.zeros(T2 + 1)
    for r in negr[negr <= T2]:
        r = int(r)
        k = np.arange(1, T2//r + 1)
        D[k*r] += phi[k]/phi[r]
    D[1:] /= A_[1:]**2
    inc = np.zeros(T2 + 1); inc[1:] = phi[1:T2 + 1]/A_[1:]**2*G_inf - D[1:]
    Ut = np.cumsum(inc)                          # Ut[A] >= E L * sup_{block A} R^m
    U = Ut/EI
    # sanity: direct R^m at a few x
    Gc = np.concatenate([[0.0], np.cumsum(np.where(mu[1:RMAX+1] == -1, 1.0/(r_all[1:RMAX+1].astype(float)**2*phi[1:RMAX+1]), 0.0))])
    for x in [1.5*N0 - 0.5, 3.7*N0, 50.2*N0]:
        m = int(x); A = m//N0
        k = np.arange(1, A + 1)
        direct = np.sum(phi[k]/k**2*(Gc[np.minimum(m//k, RMAX)] - Gc[A//k]))/EI
        print(f"# sanity R^m(x={x:.1f}) direct {direct:.8f} <= U(A={A}) {U[A]:.8f}", flush=True)
    # far R^m
    I_m = float(np.sum(nu*np.minimum(np.log(negr), L))) + L*TAILR
    sqrtsum = float(np.sum(nu*np.sqrt(negr))) + 4*RMAX**-1.5
    etaV = G_inf + 2*sqrtsum
    Rm_far = ((6/math.pi**2)*I_m + (6/math.pi**2)*c_phi*2.916/T2**2 + 2*B_phi*T2**-0.5*etaV)/EI
    print(f"# I_m={I_m:.8f}  eta^1/2 V_m<={etaV:.6f}  Rm_far(t<eta/T2)<={Rm_far:.6f}  max U on A in [1,T1)={U[1:T1].max():.6f} "
          f"max U on [T1,T2]={U[T1:].max():.6f}  U(T2)={U[T2]:.6f}  C_G I_m/I_w={1.2687739*I_m/Iw:.6f}", flush=True)
    for S in subsets:
        a = f0*factor_table(S)[sig]; a[0] = 0.0; a /= nn
        F = np.cumsum(a)
        A = np.arange(T1)
        val = (F[(A + 1)*N0 - 1] - F[A])/EI
        c = np.arange(1, T1 + 1)
        pw = (F[c*N0] - F[c - 1])/EI
        cS = cS_of(S, c0)
        es_num = Esup(F, cS, T1, NS)
        es_an = 2*B_half(S)/math.sqrt(NS)
        epsS = max(es_num, es_an) + ESLACK
        farS = 1 + 2*epsS/EI
        plus_near = val + U[A]
        iA = int(np.argmax(plus_near))
        plus_mid = farS + U[T1:T2 + 1].max()
        plus_far = farS + Rm_far
        best = max(plus_near.max(), plus_mid, plus_far)
        results.append(dict(S=S, Rmax=float(val.max()), tR=1/(int(np.argmax(val)) + 1), pw=float(pw.max()),
                            plus=best, where=('near A=%d (t/eta in (1/%d,1/%d))' % (iA, iA + 1, max(iA, 1)) if best == plus_near.max()
                                              else ('mid' if best == plus_mid else 'far')),
                            plus_lt_eta=float(max(plus_near[1:].max(), plus_mid, plus_far)),
                            es_num=es_num, es_an=es_an, farS=farS, Mloc=float(max(val.max(), farS))))
        r = results[-1]
        print(f"S={S}: ess sup R={r['Rmax']:.6f} (block A={int(np.argmax(val))}, t=eta/{int(np.argmax(val))+1}+) pointwise sup={r['pw']:.6f} | "
              f"sup R^+={best:.6f} [{r['where']}] | sup_(t<eta) R^+={r['plus_lt_eta']:.6f} | |E_S| num={es_num:.2e} an={es_an:.2e} far R_S<={farS:.6f}  [{time.time()-t00:.0f}s]", flush=True)
else:
    nb = int(math.log(NS)/delta) + 3
    ih = int(L/delta)
    hk = np.sin(math.pi*np.arange(ih + 1)*delta/L)**2
    lip_h = math.pi/L
    # ---- R^m (S independent)
    XT2 = math.log(T2*N0)
    Imax = int(XT2/delta) + 3
    rb = np.floor(np.log(negr)/delta).astype(np.int64)
    nubins = np.bincount(rb, weights=nu, minlength=Imax + 1)[:Imax + 1]
    Aconv = fftconvolve(nubins, hk)[:Imax + 1]
    cnu = np.concatenate([[0.0], np.cumsum(nubins)])
    i = np.arange(Imax + 1)
    lo = np.clip(i - ih - 1, 0, Imax + 1); hi = np.clip(i + 2, 0, Imax + 1)
    AU = np.maximum(Aconv, 0) + lip_h*delta*(cnu[hi] - cnu[lo]) + TAILR
    yv = i*delta
    hy = np.where(yv <= L, np.sin(math.pi*yv/L)**2, 0.0)
    mtU = np.maximum(AU - hy, 0.0)
    ystar = (L/math.pi)*math.asin(math.sqrt(G_inf))
    ylo = L - ystar
    # PROVED: mt(u)=0 for y=log(1/u) <= L - ystar (h increasing on [0,L/2]; h >= G_inf on [ystar, L-ystar]).
    # The binning allowance makes mtU slightly positive there (h tiny); zero it by the proof.
    n_junk = int(np.count_nonzero(mtU[yv <= ylo] > 0)); junk_max = float(mtU[yv <= ylo].max()) if n_junk else 0.0
    mtU[yv <= ylo] = 0.0
    print(f"# zeroed {n_junk} grid values of mtU below proved support (max {junk_max:.2e})", flush=True)
    nz = np.nonzero(mtU > 0)[0]
    print(f"# mt^U: sup={mtU.max():.6e} at u/eta={math.exp(L - nz[np.argmax(mtU[nz])]*delta):.4f}; support (grid) y in [{nz[0]*delta:.4f},{nz[-1]*delta:.4f}] "
          f"i.e. u/eta <= {math.exp(L - nz[0]*delta):.4f}; proved support y >= L - ystar = {ylo:.4f} (u/eta <= {math.exp(ystar):.4f})", flush=True)
    assert nz[0]*delta >= ylo - 2*delta
    Lam_m = lip_h*(G_inf + 1)
    i0 = int(ylo/delta)
    I_m = delta*(mtU[i0:].sum() + Lam_m*delta*(Imax + 1 - i0)) + 1.458*math.exp(-2*(Imax*delta - L))
    etaV = lip_h*(2*(G_inf + 1) + 1.944)
    K = int(math.exp(XT2 - ylo + 3*delta)) + 2
    assert K <= NMAX
    kk = np.arange(1, K + 1)
    kap = phi[1:K + 1]/kk.astype(np.float64)**2
    kb = np.floor(np.log(kk)/delta).astype(np.int64)
    kbins = np.bincount(kb, weights=kap, minlength=Imax + 1)[:Imax + 1]
    Rmconv = fftconvolve(kbins, mtU)[:Imax + 1]
    ck = np.concatenate([[0.0], np.cumsum(kbins)])            # ck[i] = sum_{b<i} kbins[b]
    # Lipschitz allowance only for bins b with (j-b)delta >= ylo - delta (else X - log k < ylo and mt = 0 exactly)
    ilo = int(math.floor(ylo/delta)) - 1
    jj = np.arange(Imax + 1)
    ck1 = ck[np.clip(jj - ilo + 1, 0, Imax + 1)]
    RmU = (np.maximum(Rmconv, 0) + Lam_m*delta*ck1)/EI       # cell j: X in [j delta, (j+1) delta]
    Rm_far = ((6/math.pi**2)*I_m + (6/math.pi**2)*c_phi*2.916/T2**2 + 2*B_phi*T2**-0.5*etaV)/EI
    jT2 = int(XT2/delta) - 1
    print(f"# R^m: sup over x<=T2 N0 = {RmU[:jT2].max():.6e} at t/eta={math.exp(L - np.argmax(RmU[:jT2])*delta):.4f}; "
          f"I_m<={I_m:.6e} (C_G I_m/I_w={1.2687739*I_m/Iw:.2e}); eta^1/2 V_m<={etaV:.4f}; Rm_far<={Rm_far:.6e}; K={K}  [{time.time()-t00:.0f}s]", flush=True)
    jNS = int(math.log(NS)/delta) - 2
    j = np.arange(jNS + 1)
    Xj = j*delta
    for S in subsets:
        a = f0*factor_table(S)[sig]; a[0] = 0.0; a /= nn
        F = np.cumsum(a)
        b = np.floor(np.log(np.arange(1, NS + 1))/delta).astype(np.int64)
        mb = np.bincount(b, weights=a[1:], minlength=nb)
        conv = fftconvolve(mb, hk)[:jNS + 1]
        cm = np.concatenate([[0.0], np.cumsum(mb)])
        lo = np.clip(j - ih - 1, 0, nb); hi = np.clip(j + 2, 0, nb)
        RU = (np.maximum(conv, 0) + lip_h*delta*(cm[hi] - cm[lo]))/EI
        cS = cS_of(S, c0)
        es_num = Esup(F, cS, T1 - 1, NS)     # mid cells start at x >= NS e^{-2 delta}, i.e. s >= log(T1) - 2 delta
        es_an = 2*B_half(S)/math.sqrt(NS)
        epsS = max(es_num, es_an) + ESLACK
        farS = 1 + 2*epsS/EI
        plus = RU + RmU[:jNS + 1]
        ip = int(np.argmax(plus)); iR = int(np.argmax(RU))
        plus_mid = farS + RmU[jNS:jT2].max()
        plus_far = farS + Rm_far
        best = max(plus[ip], plus_mid, plus_far)
        m3 = Xj > L - math.log(3); m1 = Xj > L
        results.append(dict(S=S, Rmax=float(RU[iR]), tR=math.exp(L - Xj[iR]), plus=best,
                            where=('near t/eta=%.4f' % math.exp(L - Xj[ip]) if best == plus[ip] else ('mid' if best == plus_mid else 'far')),
                            plus_lt3=float(max(plus[m3].max(), plus_mid, plus_far)), plus_lt1=float(max(plus[m1].max(), plus_mid, plus_far)),
                            Rm_at_peak=float(RmU[iR]), es_num=es_num, es_an=es_an, farS=farS, Mloc=float(max(RU.max(), farS))))
        r = results[-1]
        print(f"S={S}: sup R^U={r['Rmax']:.6f} at t/eta={r['tR']:.4f} (R^m there {r['Rm_at_peak']:.2e}) | sup R^+={best:.6f} [{r['where']}] | "
              f"sup_(t<3eta) R^+={r['plus_lt3']:.6f} sup_(t<eta) R^+={r['plus_lt1']:.6f} | |E_S| num={es_num:.2e} an={es_an:.2e} far R_S<={farS:.6f} [{time.time()-t00:.0f}s]", flush=True)

M = max(r['Mloc'] for r in results)
# R_S(t) - R_S1(t) = sum_{m>=2} (lam(m)/m)(R_S1(tm) - R_S1(t)), sum_{m>=2} lam(m)/m = 0, 0 <= R_S1 <= M
#   <= sigma_+ (M - R(t)) + sigma_- R(t) = sigma M,  sigma_+ = sigma_- = (prod-1)/2.
slack = M*PROD/2
best = max(results, key=lambda r: r['plus'])
bestR = max(results, key=lambda r: r['Rmax'])
print(f"# SUMMARY kind={kind} eta=1/{N0}: signed sup_(S1,t) R = {bestR['Rmax']:.6f} (S={bestR['S']}); "
      f"max_(S1) sup R^+ = {best['plus']:.6f} (S={best['S']}, {best['where']}); M={M:.5f}; slack={slack:.2e}; "
      f"C_T^+ <= {best['plus'] + slack:.6f} -> {math.ceil((best['plus'] + slack)*1e5)/1e5:.5f}", flush=True)
if kind == 'sharp':
    print(f"#   sup over t<eta (mu^- region) of R^+ (max over S1) = {max(r['plus_lt_eta'] for r in results):.6f}; "
          f"pointwise sup R (S=[]) = {results[0]['pw']:.6f}", flush=True)
else:
    print(f"#   sup over t<3eta of R^+ = {max(r['plus_lt3'] for r in results):.6f}; over t<eta: {max(r['plus_lt1'] for r in results):.6f}", flush=True)
print(f"# total time {time.time()-t00:.0f}s")
