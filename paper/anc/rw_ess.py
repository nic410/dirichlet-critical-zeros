"""Gauss-transfer Farey profile: R_w = ess sup_t P_w(t),
   P_w(t) = sum_k (phi(k)/k^2) Wt(k t) / ((6/pi^2) I_w),   Wt(u) = u^2 w(u) = h(log 1/u).
Sharp w = u^-2 1_[eta,1]: step function in x=1/t, constant on (m,m+1) (breakpoints x in Z since 1/eta = N0 in Z):
   ess sup = max_A [Phi((A+1)N0-1) - Phi(A)]/((6/pi^2)L),  pointwise sup = max_c [Phi(c N0) - Phi(c-1)]/(...)
   (Phi(m) = sum_{k<=m} phi(k)/k^2).
Log-smooth: binned upper bound with allowance (pi/L)*delta*mass (rigorous for every X in each cell).
Far region x > NS (Y > L): P_w(t) <= 1 + 2 sup_{s >= log(NS/N0)} |E_phi(s)| / ((6/pi^2) I_w),
   E_phi(s) = Phi(e^s) - (6/pi^2)(s + c_phi),  |E_phi(s)| <= 2 (zeta(3/2)/zeta(3)) e^{-s/2} (proved) beyond NS.
C_w = C_G * R_w, C_G = 6/(pi^2 E) = 1.2687739...
usage: python3 rw_ess.py  (runs all eta)"""
import math, numpy as np, time
from scipy.signal import fftconvolve
from arith_lib import spf_sieve, primes_from_spf, phi_mu, GAMMA, E_and_c
NS = 10**7
t0 = time.time()
spf = spf_sieve(NS); P = primes_from_spf(spf); phi, mu = phi_mu(NS, P)
k = np.arange(NS + 1, dtype=np.float64); k[0] = 1
a = phi/k**2; a[0] = 0.0
Phi = np.cumsum(a)
c6 = 6/math.pi**2
c_phi = GAMMA + 0.5699610427687271
B_phi = 2.6123753486854883/1.2020569031595942
E_lo, E_hi, c0, _ = E_and_c(10**7)
CG = c6/E_hi
print(f"# C_G = 6/(pi^2 E) = {CG:.9f};  NS={NS}", flush=True)
delta = 2e-5
b = np.floor(np.log(np.arange(1, NS + 1))/delta).astype(np.int64)
mb = np.bincount(b, weights=a[1:])
cm = np.concatenate([[0.0], np.cumsum(mb)])
for N0 in [10, 100, 1000, 10**4, 10**5]:
    L = math.log(N0); eta = 1/N0
    T1 = NS//N0
    n = np.arange(T1, NS, dtype=np.float64)
    ephi = max(np.abs(Phi[T1:NS] - c6*(np.log(n) + c_phi)).max(), np.abs(Phi[T1:NS] - c6*(np.log(n + 1) + c_phi)).max())
    eps = max(ephi, 2*B_phi/math.sqrt(NS)) + 1e-9
    # sharp
    A = np.arange(T1)
    ess = (Phi[(A + 1)*N0 - 1] - Phi[A])/(c6*L)
    c = np.arange(1, T1 + 1)
    pw = (Phi[c*N0] - Phi[c - 1])/(c6*L)
    far = 1 + 2*eps/(c6*L)
    Rs = max(ess.max(), far)
    iA = int(np.argmax(ess)); ic = int(np.argmax(pw))
    print(f"sharp     eta=1e-{round(math.log10(N0))}: ess sup R_w = {Rs:.6f} (block A={iA}: t in (eta/{iA+1}, eta/{max(iA,1)})"
          f"{' i.e. t -> eta+' if iA==0 else ''}); pointwise sup = {pw.max():.6f} (at t = eta/{ic+1}); far<= {far:.5f}; "
          f"C_w = C_G R_w = {CG*Rs:.4f} (pointwise {CG*pw.max():.4f})", flush=True)
    # log-smooth
    Iw = L/2
    ih = int(L/delta)
    hk = np.sin(math.pi*np.arange(ih + 1)*delta/L)**2
    jNS = int(math.log(NS)/delta) - 2
    conv = fftconvolve(mb, hk)[:jNS + 1]
    j = np.arange(jNS + 1)
    lo = np.clip(j - ih - 1, 0, len(mb)); hi = np.clip(j + 2, 0, len(mb))
    PU = (np.maximum(conv, 0) + (math.pi/L)*delta*(cm[hi] - cm[lo]))/(c6*Iw)
    far = 1 + 2*eps/(c6*Iw)
    ip = int(np.argmax(PU))
    Rl = max(PU.max(), far)
    print(f"logsmooth eta=1e-{round(math.log10(N0))}: ess sup R_w <= {Rl:.6f} at t/eta={math.exp(L - ip*delta):.4f} (grid value without allowance "
          f"{conv[ip]/(c6*Iw):.6f}); far<= {far:.5f}; C_w = {CG*Rl:.4f}   [{time.time()-t0:.0f}s]", flush=True)
