# Independent check: brute-force the Toeplitz identity (lem:toeplitz) with explicit primitive characters,
# the Omega formula (two forms), c(q,e), mu_Omega mass = H, and the Q-rough failure mode.
import numpy as np, math, cmath, itertools, random
from sympy import factorint, primerange, totient, mobius, divisors, primitive_root

def unit_group_chars(q):
    """All characters mod q as dicts a->value (a in units), built from CRT + cyclic factors."""
    if q == 1:
        return [ {0: 1.0+0j} ]
    fac = factorint(q)
    comps = []   # list of (modulus m=p^k, list of (generator g, order o)) ; char on component
    for p, k in fac.items():
        m = p**k
        if p == 2:
            if k == 1: gens = []
            elif k == 2: gens = [(m-1, 2)]
            else: gens = [(m-1, 2), (5, 2**(k-2))]
        else:
            gens = [(primitive_root(m), (p-1)*p**(k-1))]
        comps.append((m, gens))
    # discrete log tables for each component
    tables = []
    for m, gens in comps:
        tab = {}
        orders = [o for g, o in gens]
        for exps in itertools.product(*[range(o) for o in orders]):
            x = 1
            for (g, o), e in zip(gens, exps):
                x = x*pow(g, e, m) % m
            tab[x] = exps
        tables.append((m, orders, tab))
    units = [a for a in range(q) if math.gcd(a, q) == 1]
    allorders = [o for (m, orders, tab) in tables for o in orders]
    chars = []
    for js in itertools.product(*[range(o) for o in allorders]):
        ch = {}
        for a in units:
            ang = 0.0; idx = 0
            for (m, orders, tab) in tables:
                ex = tab[a % m]
                for o, e in zip(orders, ex):
                    ang += js[idx]*e/o; idx += 1
            ch[a] = cmath.exp(2j*math.pi*ang)
        chars.append(ch)
    return chars

def is_primitive(ch, q):
    for d in divisors(q):
        if d == q: continue
        # induced from mod d iff chi(a)=1 for all units a == 1 mod d
        if all(abs(ch[a]-1) < 1e-9 for a in ch if a % d == 1 % d):
            return False
    return True

def chi_val(ch, q, n):
    a = n % q
    return ch.get(a, 0.0) if math.gcd(n, q) == 1 else 0.0

Q = 24
random.seed(1)
wvals = {q: random.uniform(0.2, 2.0) if q >= 5 else 0.0 for q in range(1, Q+1)}   # w(q/Q), zero below eta Q
omega = {q: wvals[q]*q/float(totient(q)) for q in range(1, Q+1)}
prim = {}
for q in range(1, Q+1):
    if wvals[q] == 0: continue
    prim[q] = [ch for ch in unit_group_chars(q) if is_primitive(ch, q)]
    phistar = sum(1 for _ in prim[q])
    # phi*(q) check
    expect = sum(mobius(q//d)*totient(d) for d in divisors(q))
    assert phistar == expect, (q, phistar, expect)

def Delta(n, m):
    s = 0j
    for q, chs in prim.items():
        for ch in chs:
            s += omega[q]*chi_val(ch, q, n)*np.conj(chi_val(ch, q, m))
    return s

def k_omega(h):
    s = 0.0
    ds = range(1, Q+1) if h == 0 else [d for d in divisors(abs(h)) if d <= Q]
    for d in ds:
        s += float(totient(d))*sum(float(mobius(j))*omega[d*j] for j in range(1, Q//d+1))
    return s

def Omega1(e):
    s = 0.0
    for r in range(1, Q//e+1):
        if mobius(r) != 0 and math.gcd(r, e) == 1:
            s += float(mobius(r))*omega[e*r]/r
    return float(totient(e))/e*s

def Omega2(e):
    s = 0.0
    for r in range(1, Q//e+1):
        if mobius(r) != 0 and math.gcd(r, e) == 1:
            s += float(mobius(r))/float(totient(r))*wvals[e*r]
    return s

def ramanujan(e, h):
    return sum(math.cos(2*math.pi*c*h/e) for c in range(1, e+1) if math.gcd(c, e) == 1)

# c(q,e) formula
maxdev = 0
for q in range(1, Q+1):
    for e in divisors(q):
        c = sum(float(mobius(q//d))*float(totient(d))/d for d in divisors(q) if d % e == 0)
        s = q//e
        pred = (float(totient(e))/e*float(mobius(s))/s) if (mobius(s) != 0 and math.gcd(s, e) == 1) else 0.0
        maxdev = max(maxdev, abs(c-pred))
print("c(q,e) formula max dev:", maxdev)
print("Omega two forms max dev:", max(abs(Omega1(e)-Omega2(e)) for e in range(1, Q+1)))
dev = 0
for h in range(-60, 61):
    dev = max(dev, abs(k_omega(h) - sum(Omega2(e)*ramanujan(e, h) for e in range(1, Q+1))))
print("k_omega(h) vs sum_e Omega(e) c_e(h), |h|<=60, max dev:", dev)
H = sum(omega[q]*len(prim[q]) for q in prim)
print("H =", H, " k_omega(0) =", k_omega(0), " sum Omega(e)phi(e) =", sum(Omega2(e)*float(totient(e)) for e in range(1, Q+1)))
rough = [p for p in primerange(Q+1, 140)] + [1, 29*31, 37*29]
dev = 0; cnt = 0
for n in rough:
    for m in rough:
        d = Delta(n, m)
        dev = max(dev, abs(d - k_omega(n-m))); cnt += 1
print(f"Q-rough pairs {cnt}: max |Delta(n,m)-k_omega(n-m)| =", dev, " (H=%.3f)" % H)
# failure off Q-rough
bad = [(2, 3), (6, 1), (5, 25), (4, 7)]
print("non-rough examples Delta vs k_omega:", [(n, m, round(Delta(n, m).real, 4), round(k_omega(n-m), 4)) for n, m in bad])
# T_omega not PSD on all vectors? check min eigenvalue of [k_omega(n-m)] on an interval
M = np.array([[k_omega(n-m) for m in range(1, 400)] for n in range(1, 400)])
print("min eig of T_omega on [1,399]:", np.linalg.eigvalsh(M).min(), " max:", np.linalg.eigvalsh(M).max())
negmass = sum(max(-Omega2(e), 0)*float(totient(e)) for e in range(1, Q+1))
print("mu_Omega^- mass:", negmass)
