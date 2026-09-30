"""Task 1: E = prod_p (1 - p^-2 - p^-3)."""
import time, numpy as np, mpmath as mp
mp.mp.dps = 50
from xcheck_common import compute_E
t0 = time.time()
E50, b = compute_E(dps=50, P0=1000, K=60)
E40, _ = compute_E(dps=40, P0=200, K=80)
print("E (P0=1000,K=60,dps50) =", mp.nstr(E50, 45))
print("E (P0=200, K=80,dps40) =", mp.nstr(E40, 45))
print("difference =", mp.nstr(E50 - E40, 3))
# independent crude check: direct product over p <= 1e8 in double + tail estimate
N = 10**8
isp = np.ones(N + 1, dtype=bool); isp[:2] = False
for i in range(2, int(N**0.5) + 1):
    if isp[i]: isp[i*i::i] = False
p = np.nonzero(isp)[0].astype(np.float64)
x = 1.0 / p
logE = np.sum(np.log1p(-x*x - x*x*x)[::-1])  # sum small terms first
# tail: sum_{p>N} p^-2 ~ 1/(N log N) (PNT); -log(1-p^-2-p^-3) ~ p^-2
tail = 1.0 / (N * np.log(N))
print(f"direct product p<=1e8: {np.exp(logE):.15f}; PNT tail estimate multiplies by exp(-{tail:.3e}) -> {np.exp(logE - tail):.15f}")
print(f"time {time.time()-t0:.1f}s")
