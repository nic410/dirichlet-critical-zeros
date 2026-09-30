# Ancillary files

These files support the paper "Simple zeros on the critical line for a weighted family of Dirichlet L-functions, from
polylogarithmic to polynomial height". Every numerical constant used in a proof is produced by a script in
this directory, and the output each script produced is shipped next to it (`*.log`, `*.json`). Paths are relative:
run each command from this directory. The directory is self-contained. The Lean project in `lean/` needs a network
connection for its dependencies (see the Lean section below). In the source repository the Lean project is at
`../../lean`; the arXiv bundle (`paper/make-arxiv-bundle.sh`) copies it to `anc/lean`.

Status words, as in the paper: **CERTIFIED** means exact rational arithmetic, or interval (ball) arithmetic with every
truncation bounded by a proved inequality. **COMPUTED** means double precision with analytic truncation bounds, and no
control of rounding.

## Contents

| file(s) | what it does | supports | status | runtime* |
|---|---|---|---|---|
| `certify.py`, `certify.log` | exact rational lower bounds for p(C) at explicit even step windows, n = 400, 800, 1600 cells | Prop. "Rational certificates" (`prop:cert`); Theorems 1.1–1.3 | CERTIFIED | 8 s |
| `convexity.py`, `convexity.log` | smallest eigenvalue of Q_{F_C} on {∫h = 0} (discretised) | Remark "Optimality", App. A.1 | COMPUTED, not used in proofs | 2 s |
| `certify_tiers.py`, `extremal.py`, `tiers.log` | the "tiers" of §8.2: shape (e) with C = 1.2688 and shape (d) with C = 4.175 | §8.2 ("Which ingredient gives what") | CERTIFIED | 35 s |
| `ctplus_arb.py`, `ctplus_arb_{sharp,lsmooth}_{100,1000,10000}.{log,json}` | **interval (Arb) upper bound for C_T^+(w) at fixed η** via Prop. `prop:CTfixed`, all 64 sets S₁, far field, slack | Theorem 1.3 (i), (ii); Table `tab:CTfixed` | **CERTIFIED** | 35 s (sharp), 90 s (log-smooth) each |
| `rw_arb.py`, `rw_arb_lsmooth_{1000,10000,100000}.{log,json}` | interval (Arb) upper bound for the Gauss-transfer constant R_w (log-smooth weight) and for C_G R_w | Theorem 1.3 (iii); Table `tab:Rw` (log-smooth rows) | **CERTIFIED** | 35 s each |
| `certify_ctplus_arb.py`, `certify_ctplus_arb.log` | reads the JSON files above and runs `certify.py` at the certified bounds | Theorem 1.3 | CERTIFIED | 9 s |
| `certify_constants_arb.py`, `certify_constants_arb.log` | interval (Arb) enclosures, with explicit tails, of the arithmetic constants of Table `tab:constants` (ℰ, C_G, c_φ, B_φ, ζ(2)ζ(3)/ζ(6), Σμ²(r)/(r²φ(r)), σ₀⁻, σ₁⁻, c_∅, max_S(c_∅−c_S), B, δ_{P₀}) and the 17 inequalities the proofs use | Table `tab:constants`; Lemmas `lem:Omega`, `lem:fS`, `lem:CTlimit`; Theorems 1.2, 1.3 | CERTIFIED | 9 s |
| `run_ctplus_arb.sh` | driver for the three rows above | | | 106 s wall on 6 cores |
| `xcheck_*.py`, `run_xcheck.sh`, `xcheck.log` | independent reimplementation (no shared code) of E, sup_t R_{S₁}(t) for all 64 S₁ at 30–50 digits, and R^m | cross-check of `ctplus_arb.py` | independent check | 104 s on 6 cores |
| `ctplus.py`, `arith_lib.py`, `ctplus_run.sh`, `ctplus_{sharp,lsmooth}_{100,1000,10000}.log` | the original double-precision evaluation of Prop. `prop:CTfixed` | Table `tab:CTfixed` (historical values) | COMPUTED; superseded by `ctplus_arb.py` | 35–47 s each |
| `certify_ctplus.py`, `certify_ctplus.log` | `certify.py` (n = 400) at the double-precision C values | Table `tab:CTfixed`, columns 6–7 | CERTIFIED given C | 1 s |
| `rw_ess.py`, `rw_ess.log` | double-precision R_w (sharp and log-smooth, η = 10⁻¹ … 10⁻⁵) | Table `tab:Rw`; Remark `rem:Rwnum` | COMPUTED (log-smooth rows superseded by `rw_arb.py`) | 5 s |
| `omega_check.c`, `omega_check.log` | brute-force check of Ω⁻(e) ≤ m(e/Q) and the location of the mass of μ_Ω⁻ at Q = 10⁶ | Lemma `lem:Omega`(b) (check only); Remark `rem:negpart` (the 64–70% figure) | COMPUTED, not used in proofs | 2 s (4 runs) |
| `toeplitz_identity_check.py`, `toeplitz_identity_check.log` | the Toeplitz identity Δ(n,m) = k_ω(n−m) with explicit primitive characters (Q = 24) | Remark `rem:toeplitz`(c) | COMPUTED, not used in proofs | 13 s |
| `lean/` | Lean 4 formalisation (sources only); see `lean/README.md` and `lean/README-H.md` | Theorem 1.1 in full (`Families.thmMain`, no hypotheses); parts of Theorem 1.2; Theorem 1.4(a) in full (`Families.Hybrid.thmH`, library `FamiliesH`, no hypotheses) | kernel-checked; standard axioms only | about 8.5 min build on 8 cores, plus dependencies |

\*Wall-clock times on one core of an Intel Xeon Platinum 8362 (2.8 GHz), unless stated otherwise.

## Requirements

- Python ≥ 3.10 with `numpy` and `scipy`. The interval certificates also need **`python-flint` ≥ 0.9**, the Python
  bindings of FLINT/Arb (`pip install python-flint`; tested with 0.9.0 = FLINT 3.6.0). The cross-check needs `mpmath`,
  and `toeplitz_identity_check.py` needs `sympy`. Tested with Python 3.10.12, numpy 2.2.6, scipy 1.15.3, mpmath 1.3.0 on
  x86_64 Linux.
- A C compiler for `omega_check.c` (`gcc -O2 -o omega_check omega_check.c -lm`).
- Memory: at most 0.9 GB per process (peak resident sizes are printed at the end of each `*_arb_*.log`).
  `run_ctplus_arb.sh` runs `JOBS=6` processes at once by default.
- Lean: `elan` (see below).

## Commands and expected output

Every command writes the file that is shipped. Compare your output with the shipped log. Timings and ball radii may
differ; the certified digits should not.

```
./run_ctplus_arb.sh                  # ctplus_arb_*.{log,json}, rw_arb_*.{log,json}, certify_ctplus_arb.log
for n in 400 800 1600; do echo "== n=$n"; python3 certify.py $n; done > certify.log
python3 convexity.py > convexity.log
python3 certify_tiers.py > tiers.log
python3 certify_constants_arb.py > certify_constants_arb.log
./run_xcheck.sh                      # xcheck.log
python3 rw_ess.py > rw_ess.log
python3 certify_ctplus.py 400 130491/100000 120423/100000 115320/100000 123617/100000 109101/100000 104331/100000 > certify_ctplus.log
python3 ctplus.py sharp 100 10000000 1000000 > ctplus_sharp_100.log         # also 1000, 10000
python3 ctplus.py lsmooth 100 10000000 1000000 2e-5 > ctplus_lsmooth_100.log # also 1000, 10000
gcc -O2 -o omega_check omega_check.c -lm
for a in "1 0.01" "1 0.001" "0 0.01" "0 0.001"; do ./omega_check 1000000 $a; done > omega_check.log
python3 toeplitz_identity_check.py > toeplitz_identity_check.log
```

`JOBS=2 ./run_ctplus_arb.sh` uses less memory. Setting `PIN="taskset -c 4-9"` (Linux) pins the jobs to CPUs.

**Output format.** In `certify.log`, `certify_ctplus.log` and the p-lines of `certify_ctplus_arb.log`, `EXACT p >= x`
and `distinct >= x` print the exact rational rounded *down* to 9 decimals, and `(certified >= y)` rounds it down to 6
decimals. `tiers.log` prints 6-decimal values rounded down. Printed lower (upper) ends of enclosures are rounded down
(up). Up to 29 September 2026 the 9-decimal values, the `tiers.log` values and some printed enclosure ends were rounded
to nearest, so some were 10⁻⁹ (in `tiers.log`, 10⁻⁶) too large; the logs above were regenerated on 30 September 2026.
Every 6-decimal certified value in `certify*.log` is unchanged. In `tiers.log` the shape-(e) values are now 0.788171 and
0.894085 (formerly 0.788172 and 0.894086), and §8.2 of the paper quotes these.

### Expected results of the interval certificates (`certify_ctplus_arb.log`)

C_T^+(w) ≤ C̄ is CERTIFIED. The maximum over S₁ is at S₁ = ∅ in all six cases. The third column is a certified
enclosure of sup_t R_∅(t): the lower end is a certified value R_∅(t₀) at one explicit point t₀. So C̄ is sharp to
about 3·10⁻⁵, and nearly all of that gap is the S-slack ½M_wδ_{P₀} of `prop:CTfixed`. The p-values are exact rational
certificates at C̄ rounded up to 5 decimals.

| weight | η | sup_t R_∅(t) ∈ | C_T^+(w) ≤ C̄ | p(C̄) ≥ (n = 1600) | (1+p)/2 ≥ |
|---|---|---|---|---|---|
| sharp | 10⁻² | [1.30486623, 1.30486628] | 1.30490441 | 0.880382 (at 1.30491) | 0.940191 |
| sharp | 10⁻³ | [1.20418914, 1.20418919] | 1.20422426 | 0.896219 (at 1.20423) | 0.948109 |
| sharp | 10⁻⁴ | [1.15315973, 1.15315977] | 1.15319336 | 0.904739 (at 1.15320) | 0.952369 |
| log-smooth | 10⁻² | [1.23609593, 1.23609620] | 1.23613220 | 0.891060 (at 1.23614) | 0.945530 |
| log-smooth | 10⁻³ | [1.09095738, 1.09095752] | 1.09098929 | 0.915569 (at 1.09099) | 0.957784 |
| log-smooth | 10⁻⁴ | [1.04325871, 1.04325881] | 1.04328919 | 0.924202 (at 1.04329) | 0.962101 |

At 4 decimals: C_T^+ ≤ 1.0910 gives p ≥ 0.915568, and C_T^+ ≤ 1.0433 gives p ≥ 0.924200 (log-smooth, η = 10⁻³ and 10⁻⁴).
Both are in the log.

The log also gives certified upper bounds for max_{S₁} sup (R_{S₁} + R^m) over the region where μ_Ω⁻ and R^m live:
t < η for the sharp weight, t < 3η for the log-smooth weight.

- sharp: 1.149557, 1.099476, 1.074595
- log-smooth: 1.136613, 1.045532, 1.028502. These are dominated by the far-field bound (b); the double-precision values
  of the actual suprema are 1.1365, 1.0357, 1.0152.

All of them are well below the maxima, so the positive part does not change any constant.

R_w (Gauss route, log-smooth weight), CERTIFIED by `rw_arb.py`:

| η | R_w ∈ | C_G R_w ≤ | used in the text | p(C_G R_w) ≥ (at C rounded up to 4 decimals) |
|---|---|---|---|---|
| 10⁻³ | [1.05981540, 1.05981551] | 1.34466628 | R_w ≤ 1.0599, C_G R_w < 1.3448 | 0.874482 (at 1.3447) |
| 10⁻⁴ | [1.02883027, 1.02883034] | 1.30535310 | R_w ≤ 1.0289, C_G R_w < 1.3055 | 0.880308 (at 1.3054) |
| 10⁻⁵ | [1.01585839, 1.01585844] | 1.28889470 | R_w ≤ 1.0159, C_G R_w < 1.2890 | 0.882814 (at 1.2889) |

The same runs certify C_G = 6/(π²ℰ) ≤ 1.26877393 < 1.268774, and the constants quoted in the lemma files: B < 3.73,
δ_{P₀} < 5.83·10⁻⁵ and σ₀⁻ < 0.33 (each is an `assert` in `ctplus_arb.py`). `certify_constants_arb.py` encloses all the
constants of Table `tab:constants` with the same code and tail bounds, adds σ₁⁻ < 0.27, Σμ²(r)/(r²φ(r)) < 1.34 and
max_S(c_∅−c_S) < 0.168 (tails stated in its header), and checks the 17 inequalities used in the text; it ends with
`SUMMARY: all 17 inequalities CERTIFIED`.

## How `ctplus_arb.py` certifies C_T^+(w)

Notation of `lemma-toeplitz-C.tex`: x = 1/t, X = log x, a_n = f_S(n)/n, EI = ℰI_w, w̃(u) = h(log(1/u)) with h = 1_{[0,L]}
(sharp) or h(y) = sin²(πy/L)1_{[0,L]} (log-smooth), L = log(1/η), η = 1/N₀. All real arithmetic is Arb ball
arithmetic at 64 bits. Every maximum and every comparison is taken on the exact dyadic endpoints of the balls.
Integers (φ, μ, factorisations, bin edges) are exact. Floating point is used only to choose grid points and to print.
The steps below follow Prop. `prop:CTfixed` and apply each of its bounds as stated.

1. **Reduction in S.** C_T^+ ≤ max over the 64 sets S₁ ⊆ {2,…,13} of ess sup_t (R_{S₁} + R^m), plus ½M_wδ_{P₀}.
   Here a_n = f_∅(n)/n · ∏_{p∈S₁} f_S(p^v)/f_∅(p^v) with v = min(v_p(n), 2), using exact rational factors.
2. **Regions.** Near: x ≤ N_S = 10⁶. Mid: N_S < x ≤ T₂N₀ with T₂ = 10⁶. Far: x > T₂N₀.
3. **R_S, near, sharp weight.** R_S is a step function. For x ∈ (m, m+1) with m = AN₀ + b, the window is n ∈ [A+1, m].
   So the essential supremum over the block A equals (F(AN₀+N₀−1) − F(A))/(EI), which is evaluated for every
   A < T₁ = N_S/N₀.
4. **R_S, near, log-smooth weight.** On [0, L], h = (1 − cos ωy)/2 with ω = 2π/L. Hence
   R_S(x) = (EI)⁻¹·½·[W₀(x) − Re(x^{iω}W₁(x))], where W₀ = Σ_{ηx<n≤x} a_n and W₁ = Σ_{ηx<n≤x} a_n n^{−iω}. This is evaluated
   from ball prefix sums at dyadic grid points x_j, with log(x_{j+1}/x_j) ≤ 1.1·10⁻³ certified. The factor n^{−iω} is
   completely multiplicative, and each p^{−iω} is computed in Arb. Between grid points, R_S is C¹ and R_S' is Lipschitz,
   because h' is (2π²/L²)-Lipschitz and vanishes at 0 and L. This gives
   sup_{[X_j,X_{j+1}]} R_S ≤ max(R_S(X_j), R_S(X_{j+1})) + (ΔX)²/8 · (EI)⁻¹(2π²/L²) Σ_{n≤x_{j+1}} a_n.
   Proof: g = R_S − (linear interpolant) vanishes at both ends, and |g''| ≤ M a.e., so |g| ≤ M(ΔX)²/8.
5. **R^m, sharp.** By `lem:Omega`(d), m̃ = 0 on [η, ∞), and m̃(u) = Σ_{μ(r)=−1, ur∈[η,1]} ν_r for u < η, with
   ν_r = 1/(r²φ(r)). For x ∈ (AN₀, (A+1)N₀), only k ≤ A contribute, and ur ≥ η forces r > A/k. So
   EI·R^m(x) ≤ U(A) := Σ_{k≤A} κ_k (G − Σ_{μ(r)=−1, r≤A/k} ν_r), with κ_k = φ(k)/k² and G ≥ σ₀⁻. U(A) is computed for all
   A ≤ T₂ from U(A) − U(A−1) = κ_A G − Σ_{r|A, μ(r)=−1} κ_{A/r}ν_r.
6. **R^m, log-smooth.** Write M(Y) = m̃(e^{−Y}). First, M = 0 for Y ≤ L − y**, where y** ≥ (L/π) arcsin √σ₀⁻. On
   [y**, L − y**] we have h ≥ σ₀⁻ ≥ Σ ν_r h(Y − log r). For Y < y** < L/2, h is nondecreasing on (−∞, L/2], so
   Σν_r h(Y − log r) ≤ σ₀⁻h(Y).
   Next, bin r and k by log r ∈ [bδ, (b+1)δ), with δ = 10⁻³ and exact integer edges ⌈e^{bδ}⌉. On a Y-cell
   [iδ, (i+1)δ], M is at most (Σ_b ν̄_b · max h on [(i−b−1)δ, (i−b+1)δ] + 3/(R₀+1)² − min(h(iδ), h((i+1)δ)))₊. This uses
   that h is unimodal and that Σ_{r>R₀} ν_r ≤ 3/(R₀+1)² (proof of `lem:Omega`), with R₀ = 10⁶. On an X-cell,
   R^m ≤ (EI)⁻¹ Σ_b κ̄_b max(M̄_{j−b−1}, M̄_{j−b}). Both convolutions are Arb polynomial products (`arb_poly`), which are
   rigorous. Every k with X − log k > L − y** for X ≤ log(T₂N₀) is included.
7. **R_S, mid and far.** Use `prop:CTfixed`(a) with T₁ = N_S/N₀ and TV(h) = 2:
   R_S ≤ 1 + 2 sup_{s≥log T₁} |E_S(s)|/(EI). On [T₁, N_S], F_S and ℰ(s + c_S) are both nondecreasing, so |E_S| is bounded
   on each bracket between consecutive checkpoints: every integer up to 2·10⁴, then ratio ≤ 1.0005. Beyond N_S,
   |E_S(s)| ≤ 2B e^{−s/2} ≤ 2·3.73/√N_S (`lem:fS`(iii)). Here c_S = c_∅ − Σ_{p∈S} log p/((p−1)(p³−p−1)).
8. **R^m, far.** Use `prop:CTfixed`(b) with T₁ := T₂ = 10⁶ and the stated bound
   V'_m ≤ 2η^{−1/2}(1 + Σ_{μ(r)=−1} r^{1/2}ν_r)TV(h). This gives
   R^m ≤ (EI)⁻¹[(6/π²)I_m + (18c_φ/π²)T₂⁻² + 8B_φ(1 + Σ r^{1/2}ν_r)T₂^{−1/2}]. For the log-smooth weight, I_m is at most
   δΣM̄_i + 1.5e^{−2(Y_top−L)}. For the sharp weight, I_m = Σ_{μ(r)=−1} ν_r min(log r, L).
9. **Slack.** M_w is at most the maximum over S₁ of max(sup_near R_{S₁}, far bound). For the sharp weight add
   1/(N₀EI): at an integer x the closed window adds a_x ≤ 1/x to the left limit, since R(x) ≤ (F(AN₀) − F(A−1))/(EI)
   for x ∈ ((A−1)N₀, AN₀]. Also δ_{P₀} ≤ 5.8243·10⁻⁵.
10. **Constants (all in Arb).**
    - ℰ: primes p ≤ 10⁷. Since every prime p > 10⁷ is ±1 mod 6, the tail product is ≥ 1 − 1/(3(P−6)) − 1/(6(P−6)²).
    - c_∅: tail ≤ 1.0001 ∫_P^∞ (t⁻² + t⁻³) log t dt.
    - B: tail ≤ exp((1+2/P)·2/√P + P⁻²).
    - δ_{P₀}: tail ≤ exp(2/(3(P−1)³)).
    - G ≥ σ₀⁻: sum over r ≤ 10⁶ plus 3/(10⁶+1)².
    - Σ_{μ(r)=−1} r^{1/2}ν_r: sum over r ≤ R₀ plus (5/3)(ζ(2)ζ(3)/ζ(6))R₀^{−3/2}. Proof: for squarefree r,
      1/(r²φ(r)) = r⁻³Σ_{d|r} μ²(d)/φ(d), and Σ_{j>z} j^{−5/2} ≤ (5/3)z^{−3/2} for all z > 0.
    - c_φ = 12 log A − log 2π, where A is Glaisher's constant; B_φ = ζ(3/2)/ζ(3).
11. **Self-checks, run every time.**
    - Sharp: the exact rational F_S(N₀−1) lies inside its ball, for four sets S.
    - Log-smooth: at the maximising grid point, a direct Arb sum Σ a_n h(log(x/n)) overlaps the prefix-sum/cosine value,
      for three sets S.
    - Independent code (`xcheck_*.py`) gives max_{S₁} sup R_{S₁}:
      - sharp: 1.3048662384, 1.2041891488, 1.1531597369
      - log-smooth: 1.2360959618, 1.0909573998, 1.0432587328
      - all six lie inside the certified enclosures.
    - Its sup R^m (log-smooth, η = 10⁻⁴: 0.0165515 at t/η = 1.210) lies below the certified bound 0.016636.

`rw_arb.py` uses the same machinery with a_k = φ(k)/k², no S, and c_w = (6/π²)I_w. Its far field is Lemma `lem:Rwfar`
(stated and proved after Lemma `lem:Rwlog`); the argument is the layer-cake proof of `lem:Rwlog`. Write c_wP_w(t) as ∫₀¹ Σ_{α_λ≤k≤β_λ} φ(k)/k² dλ, with log(β_λ/α_λ) = |{h > λ}|. For t < η/T₁ every
α_λ > T₁, so each inner sum is at most (6/π²)log(β_λ/α_λ) + 2 sup_{y≥T₁}|E_φ(y)|. Hence P_w(t) ≤ 1 + 2 sup_{y≥T₁}|E_φ(y)|/c_w.
The supremum is bracketed on [T₁, 10⁷], and |E_φ(y)| ≤ 2B_φy^{−1/2} beyond (`lem:harm`).

**Reproducibility.** The shipped logs of the interval certificates were produced by `./run_ctplus_arb.sh` from a fresh
copy of this directory on x86_64 Linux (Python 3.10.12, python-flint 0.9.0 / FLINT 3.6.0, numpy 2.2.6), with 6 jobs
pinned to 6 cores. Wall time was about 105 s. The per-run times and peak memory are at the end of each log.
All other logs were regenerated from the same fresh copy with the commands above; apart from timings they agree with
the shipped logs.

## Lean formalisation (`lean/`)

Sources only; there is no `.lake/` directory and nothing prebuilt. Start with `lean/README.md`. `lean/STATUS.md` lists
the status of each result, and `lean/STATEMENTS.md` maps Lean names to the labels of the paper.

**What the formalisation proves: Theorem 1.1.** `Families.thmMain : Families.thmMain_Statement` (theorem in
`lean/Families/Headline.lean`, statement in `lean/Families/Main.lean`) has **no hypotheses**, and
`#print axioms Families.thmMain` reports only Lean's standard axioms `[propext, Classical.choice, Quot.sound]`. In
particular nothing it depends on uses `sorry` or `native_decide`. The proof formalises the paper's argument for
Theorem 1.1, including:

* the zero side, using Weil's explicit formula from the dependency `zeta23` (below);
* the second moment;
* the Toeplitz large sieve and `C_T^+(w_η) → 1`;
* the limit step;
* the kernel-evaluated certificate p(1) ≥ 0.932282.

The classical inputs are proved too:

* the large sieve, with the absolute constant 17/4 in place of 1;
* a zero-density estimate of Montgomery's type for heights T' ≤ Q, the only range the proof uses;
* a prime number theorem with error term;
* Stirling bounds.

**What it does not prove.** Theorems 1.2 and 1.3, `thm:conditional`, Lemma A and some lemmas used only on the Gauss
route or at fixed η are stated in the Lean project (as propositions) but not proved there. There are 10 such
`Prop` definitions: `thmGauss_Statement`, `thmFixed_Statement`, `thmConditional_Statement`, `lemA_Statement`,
`lemHarm_Statement`, `lemRwlog_Statement`, `lemRwlog_numeric_Statement`, `lemWH_ratio_Statement`,
`propTI_Statement` and `propCTfixed_Statement`. `thmMain` does not depend on any of them, and the project contains
no `sorry`. These results rest on the written proofs in the paper. The fixed-η numerics
of Theorem 1.3 are certified by the interval-arithmetic scripts of this directory (CERTIFIED above), which are a
separate kind of evidence.

Lean checks the Lean statement `thmMain_Statement`. That it expresses Theorem 1.1 is a correspondence of
definitions (the family, the weights, the zero counts, p(C), the order of the limits), which a reader can check
against `lean/STATEMENTS.md`.

**Checking.** `scripts/audit.sh` repeats all of these checks mechanically, for both headlines, and ends with
`AUDIT PASSED`. It scans every declaration of both libraries (2,488 in `Families`, 567 in `FamiliesH`) for axioms and
`sorry`. It requires that `thmMain` and `Families.Hybrid.thmH` have no hypotheses, have types `thmMain_Statement` and
`thmH_Statement`, and use only the three standard axioms. It also pins the *content* of both statements and of the 31
definitions they unfold to against `scripts/Statements.baseline.txt`, so any change in meaning fails the audit. The
correspondence of `thmH_Statement` with Theorem 1.4(a) is documented in `lean/STATEMENTS-H.md`.

**Certificates.** The certificate files `Families/Certificate/{Data,EcalData}.lean` check p(1) ≥ 0.932282,
p(1.2688) ≥ 0.885912 and ℰ ≥ 0.47914 by kernel evaluation (`decide +kernel`). They were generated from `certify.py` by
small scripts that are not shipped; the data is in the `.lean` files themselves.

**What was left out.** Certificate generator scripts for the `Families` data are not included; the data are in the
`.lean` files. The generator of the hybrid certificates, `scripts/gen_hybrid_data.py`, is shipped (see
`lean/README-H.md`).

**Toolchain.** All versions are pinned in `lake-manifest.json`:

* Lean `v4.33.0-rc2` (`lean-toolchain`);
* Mathlib `51e6992efd06`;
* `Zeta23` at `fbdc36bb`, which is Anthropic's Lean formalisation of Alpöge–Furman (arXiv:2608.13637), subdirectory
  `zeta23` of https://github.com/anthropics/formal-math.

To build:

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # installs elan, if needed
cd lean
lake exe cache get          # downloads the Mathlib build cache (about 5 GB)
lake build                  # expected: "Build completed successfully"
scripts/audit.sh            # axiom / sorry audit; expected last line: "AUDIT PASSED"
```

A build of this directory, with the dependencies already downloaded and built, took about 8.5 minutes on 8 cores for both libraries
(and `scripts/audit.sh` then passed). A
fresh download of the dependencies, and building the imported `zeta23` modules, add to that.

## Polynomial height (§9: Theorem 1.4, Corollary 1.5)

These scripts come from the standalone draft of §9 and are unchanged apart from the rounding of the printed 9-decimal
values (below) and their comments, which use the paper's numbering.

They need Python 3 with numpy and scipy. Only the exact rational evaluation is certified. The floating-point step only
chooses the test function, so with other numpy/scipy/BLAS versions the printed bounds may differ in the last digit, but
they remain valid lower bounds.

| file(s) | what it does | supports | status | runtime* |
|---|---|---|---|---|
| `certify_hybrid.py`, `certify_hybrid_n400_rerun.log` (n = 400: **the values printed in the table after Theorem 1.4**), `certify_hybrid_n800.log` (n = 800: finer step functions, values larger by ≤ 10⁻⁶ for C = 1, 1.2688 and ≤ 9·10⁻⁶ for C = 4.175) | exact rational lower bounds for p(λ̄(κ); F_C) at explicit even step windows on [−λ̄/2, λ̄/2], λ̄(κ) = (2+κ)/(1+κ), κ ∈ {0, 1/4, 1/2, 1, 2, 3, 5, 10}, C ∈ {1, 1.2688, 2, 4.175}; also the "no flattening" shape `Calpha` quoted in §9.6 | Prop. `H:prop:cert`; the table after Theorem 1.4 | CERTIFIED (only the exact evaluation is part of the proof) | 4 s at n = 400, 26 s at n = 800 |
| `certify_dyadic.py`, `certify_hybrid_dyadic_n400.log`, `certify_dyadic_n400_rerun.log` | the same for C = 5.5657 ≥ 8/(3ℰ) (dyadic family) | Corollary 1.5 | CERTIFIED | 1 s |
| `classical_constant_check.py`, `classical_constant_check.log` | exact check that C_cl(1_[η,1]) = 2/(ℰ(1−η²)) ≤ 4.175 for η ≤ 0.0146 with the certified ℰ ≥ 0.47914533 (threshold 0.0146911; fails at η = 0.0147), and 8/(3ℰ) ≤ 5.5657 | Theorem 1.4(c), Corollary 1.5 | CERTIFIED | < 1 s |
| `kappa_curve.py`, `kappa_curve.log` | floating-point curve κ ↦ p(λ̄(κ); F_C), and the single-prime-modulus constants of Hua–Yang (arXiv:2609.27808, Remark 2.4) | §9.6 and §1.2 (values quoted as floating point, not certified) | COMPUTED, not used in proofs | 4 s |

Commands (from this directory):

```
OMP_NUM_THREADS=1 python3 certify_hybrid.py 400  > certify_hybrid_n400_rerun.log   # the table after Theorem 1.4
OMP_NUM_THREADS=1 python3 certify_hybrid.py 800  > certify_hybrid_n800.log         # finer step functions
OMP_NUM_THREADS=1 python3 certify_dyadic.py 400  > certify_hybrid_dyadic_n400.log  # (certify_dyadic_n400_rerun.log is the same run)
python3 classical_constant_check.py              > classical_constant_check.log
python3 kappa_curve.py                           > kappa_curve.log
```

**Output format.** In each line, `EXACT p >= x` and `distinct >= x` print the exact rational rounded *down* to 9
decimals, and `(certified >= y)` rounds it down to 6 decimals; the table after Theorem 1.4 prints the 6-decimal
values. (Up to 28 September 2026 the 9-decimal values were rounded to nearest, so some were 10⁻⁹ too large; the
6-decimal values, and therefore the paper, were not affected.)

**Reruns.** On 2026-09-28 the four scripts were rerun from this directory on x86_64 Linux (numpy 2.2.6, scipy 1.15.3),
one core each. `classical_constant_check.log` and `kappa_curve.log` were reproduced byte for byte. (On 30 September
2026 `classical_constant_check.py` and the header line of `certify_dyadic.py` were changed to print upper bounds rounded
up rather than to nearest, and their logs were regenerated; no number used in the paper changed.) The three
`certify_*` logs were regenerated with the rounded-down output; every float value and every 6-decimal certified value
is identical to the earlier run (numpy 2.5.3, scipy 1.18.1), and the 9-decimal values differ only by the change from
rounding to nearest to rounding down (at most 10⁻⁹).

**Independent checks** (not shipped). Two referee implementations share no code with
`certify_hybrid.py`; each has its own optimiser at n = 600 and its own exact evaluator. Their optimisers give values
larger than the n = 400 table by at most 6·10⁻⁶, and within 2.9·10⁻⁶ of the n = 800 values. Re-evaluating all 31
n = 400 step functions of the table with one of the independent evaluators gives identical rationals. A coarser
cross-check (m = 120 cells) agrees to within 2.7·10⁻⁵.

**Lean.** The Lean project in `lean/` contains two libraries: `Families` (Theorem 1.1, headline `Families.thmMain`)
and `FamiliesH` (Theorem 1.4(a), headline `Families.Hybrid.thmH`, no hypotheses, only the three standard axioms).
`FamiliesH` imports `Families` without modifying it. Its kernel-checked certificate data are the n = 400 step
functions of the sharp column (a) at κ = 1, 2, 3, 5, 10, i.e. the values printed in the table after Theorem 1.4.
`lean/scripts/audit.sh` checks both headlines. See `lean/README-H.md` and `lean/STATEMENTS-H.md`.

## Licence

Everything in this directory is licensed under the Apache License 2.0: the scripts, the logs, this `README.md`, and
the Lean formalisation in `lean/` including its Markdown documentation (see the `LICENSE` file at the top level of the
repository or ancillary bundle). The paper itself (its TeX sources and PDF) is licensed under CC BY 4.0
(`LICENSE-CC-BY-4.0`). (The Lean dependencies are not shipped here;
Mathlib and `zeta23`, i.e. `anthropics/formal-math`, are Apache-2.0.)
